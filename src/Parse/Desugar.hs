{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE OverloadedStrings      #-}
{-# LANGUAGE TypeOperators          #-}

module Parse.Desugar
  ( run
  ) where

import           Common
import           Introspect
import qualified Parse.Mixfix        as Mixfix
import           Parse.State
import           Praxis
import           Print
import           Stage
import           Term

import           Control.Applicative (liftA3)
import           Control.Arrow       (left)
import           Control.Monad       (unless)
import           Data.Array          (array, assocs, bounds, elems, indices,
                                      listArray, (!), (//))
import           Data.Either         (partitionEithers)
import           Data.Graph          (Graph, Vertex, reachable, vertices)
import           Data.List           (intersect, intersperse, nub, partition,
                                      (\\))
import           Data.Map.Strict     (Map)
import qualified Data.Map.Strict     as Map
import           Data.Maybe          (catMaybes, fromJust, isNothing,
                                      listToMaybe, mapMaybe)
import           Data.Monoid         ((<>))
import           Data.Set            (Set)
import qualified Data.Set            as Set
import           Prelude             hiding (exp)


run :: IsTerm a => Annotated Initial a -> Praxis (Annotated Parse a)
run term = do
  term <- desugar term
  display Parse "desugared term" term `ifFlag` debug
  return term

desugar :: IsTerm a => Annotated Initial a -> Praxis (Annotated Parse a)
desugar term = ($ term) $ case typeof (view value term) of
  BindT           -> auto
  DataConT        -> auto
  ExpT            -> desugarExp
  PatT            -> desugarPat
  ProgramT        -> desugarProgram
  TypeT           -> desugarType
  KindT           -> auto
  QTypeT          -> auto
  TypePatT        -> auto
  TypeConstraintT -> auto
  ty              -> error (show ty)
  where
    auto :: (IsTerm a, Annotation Initial a ~ Annotation Parse a) => Annotated Initial a -> Praxis (Annotated Parse a)
    auto = value (recurseTerm desugar)


desugarProgram :: Annotated Initial Program -> Praxis (Annotated Parse Program)
desugarProgram (a :< Program decls) = do
  decls <- (catMaybes <$> traverse desugarDecl decls) >>= coalesceDecls
  return (a :< Program decls)

collectFreeVars :: Annotated Initial Exp -> Set Name
collectFreeVars x = collectFreeVars' x where
  collectFreeVars' :: IsTerm a => Annotated Initial a -> Set Name
  collectFreeVars' (_ :< x) = case typeof x of
    ExpT -> case x of
      Var n -> Set.singleton n
      _     -> continue
    DeclTermT -> case x of
      DeclTermVar n _ e -> Set.delete n (collectFreeVars' e)
      _                 -> continue
    _     -> continue
    where continue = getConst $ recurseTerm (Const . collectFreeVars') x


-- Helper for desugaring "&". It turns top-level VarRefSugar into Var and returns the name of such variables
desugarExpRef :: Annotated Initial Exp -> Praxis (Annotated Parse Exp, Set Name)
desugarExpRef (a :< exp) = case exp of

  Sig exp ty -> do
    (exp, readVars) <- desugarExpRef exp
    ty <- desugarType ty
    return (a :< Sig exp ty, readVars)

  Pair exp1 exp2 -> do
    (exp1, readVars1) <- desugarExpRef exp1
    (exp2, readVars2) <- desugarExpRef exp2
    return (a :< Pair exp1 exp2, readVars1 `Set.union` readVars2)

  VarRefSugar var -> return (a :< Var var, Set.singleton var)

  _ -> do
    exp <- desugarExp (a :< exp)
    return (exp, Set.empty)


desugarExp :: Annotated Initial Exp -> Praxis (Annotated Parse Exp)
desugarExp (a@(src, _) :< exp) = case exp of

  Apply f x -> do
    f <- desugarExp f
    let freeVars = collectFreeVars x
    (x, readVars) <- desugarExpRef x
    let mixedVars = freeVars `Set.intersection` readVars
    when (not (null mixedVars)) $ throwAt Parse src $ "variable(s) " <> separate ", " (map pretty (Set.elems mixedVars)) <> " used in a read context"
    let unrollReads []     = (a :< Apply f x)
        unrollReads (v:vs) = (a :< Read v (unrollReads vs))
    return (unrollReads (Set.elems readVars))

  DoSugar stmts -> desugarStmts stmts where
    desugarStmts :: [Annotated Initial Stmt] -> Praxis (Annotated Parse Exp)
    desugarStmts [stmt]
      | (_ :< StmtExp exp)   <- stmt = desugarExp exp
      | (_ :< StmtBind bind) <- stmt = throwAt Parse (view source stmt) ("do block must end in an expression" :: String)
    desugarStmts (stmt:stmts)
      | (_ :< StmtExp exp) <- stmt = do
        exp1 <- desugarExp exp
        exp2 <- desugarStmts stmts
        let a = (view source exp1 <> view source exp2, Nothing)
        return (a :< Seq exp1 exp2)
      | (_ :< StmtBind bind) <- stmt = do
        bind <- desugar bind
        exp <- desugarStmts stmts
        let a = (view source bind <> view source exp, Nothing)
        return (a :< Let bind exp)

  -- Call Mixfix.parse to fold the token sequence into a single expression, then desugar that expression
  MixfixSugar tokens -> Mixfix.parse src tokens >>= desugar

  VarRefSugar var -> throwAt Parse src $ "observed variable " <> pretty var <> " is not in a valid read context"

  Con "True" -> pure (a :< Lit (Bool True))

  Con "False" -> pure (a :< Lit (Bool False))

  Where exp decls -> do
    exp <- desugarExp exp
    decls <- traverse (desugarDeclTerm False) decls >>= coalesceDeclTerms
    return (a :< Where exp decls)

  _           -> (a :<) <$> recurseTerm desugar exp


desugarOp :: Annotated Initial Op -> Praxis (Annotated Parse Op)
desugarOp op@(a@(src, _) :< Op parts) = do

  let
    hasConsecutiveHoles :: [Maybe Name] -> Bool
    hasConsecutiveHoles = \case
      (Nothing:Nothing:ps) -> True
      []                   -> False
      (p:ps)               -> hasConsecutiveHoles ps

  when (hasConsecutiveHoles parts) $ throwAt Parse src $ "op " <> pretty op <> " has two consecutive holes"
  return (a :< Op parts)


desugarPrec :: Annotated Initial Prec -> Praxis (Annotated Parse Prec)
desugarPrec (a@(src, _) :< Prec ord op) = do

  op <- desugarOp op

  -- check the op exists
  opDefinitions <- use (parseState . opState . definitions)
  unless (op `Map.member` opDefinitions) $ throwAt Parse src $ "unknown op " <> pretty op

  return (a :< Prec ord op)


desugarOpRules :: Annotated Parse Op -> Annotated Initial OpRules -> Praxis (Maybe Assoc, [Annotated Parse Prec])
desugarOpRules op ((src, _) :< OpRules rules) = do

    let (assocs, precs) = partitionEithers rules

    when (length assocs > 1) $ throwAt Parse src $ "more than one associativity specified for op " <> pretty op
    when (length precs > 1) $ throwAt Parse src $ "more than one precedence block specified for op " <> pretty op

    precs <- mapM desugarPrec (concat precs)
    return (listToMaybe assocs, precs)


desugarDecl :: Annotated Initial Decl -> Praxis (Maybe (Annotated Parse Decl))
desugarDecl (a@(src, _) :< decl) = case decl of

  DeclOpSugar op name rules -> do

    op@(_ :< Op parts) <- desugarOp op
    (assoc, precs) <- desugarOpRules op rules

    let checkNoAssoc = unless (isNothing assoc) $ throwAt Parse src $ "associativity can not be specified for non-infix op " <> pretty op
    fixity <- case (head parts, last parts) of
      (Nothing, Nothing) -> return (Infix assoc)
      (Nothing,  Just _) -> checkNoAssoc >> return Postfix
      (Just _,  Nothing) -> checkNoAssoc >> return Prefix
      (Just _,   Just _) -> checkNoAssoc >> return Closed

    registerOp src op (name, fixity) precs

    return Nothing


  DeclRec decls -> do
    decls <- traverse desugarDeclRec decls >>= coalesceDeclRecs
    return $ Just (a :< DeclRec decls)

  DeclSynSugar name ty -> do
    ty <- desugar ty
    parseState . typeSynonyms %= Map.insert name ty
    return Nothing

  DeclTerm decl -> do
    decl <- desugarDeclTerm False decl
    return $ Just (a :< DeclTerm decl)

  DeclType decl -> do
    decl <- desugarDeclType False decl
    return $ Just (a :< DeclType decl)


desugarDeclRec :: Annotated Initial DeclRec -> Praxis (Annotated Parse DeclRec)
desugarDeclRec (a@(src, _) :< decl) = (a :<) <$> case decl of

  DeclRecTerm decl -> DeclRecTerm <$> desugarDeclTerm True decl

  DeclRecType decl -> DeclRecType <$> desugarDeclType True decl


expIsFunction :: Annotated s Exp -> Bool
expIsFunction (_ :< exp) = case exp of
  Lambda _ _ -> True
  Cases  _   -> True
  _          -> False


desugarDeclTerm :: Bool -> Annotated Initial DeclTerm -> Praxis (Annotated Parse DeclTerm)
desugarDeclTerm recursive (a@(src, _) :< decl) = (a :<) <$> case decl of

  DeclTermDefSugar name args exp -> do
    args <- mapM desugarPat args
    let
      curry :: [Annotated Parse Pat] -> Annotated Parse Exp -> Annotated Parse Exp
      curry []     e = e
      curry (p:ps) e = (view source p <> view source e, Nothing) :< Lambda p (curry ps e)
    exp <- curry args <$> desugarExp exp
    when (recursive && not (expIsFunction exp)) $ throwAt Parse src $ "non-function " <> pretty name <> " can not be recursive"
    return $ DeclTermVar name Nothing exp

  DeclTermSigSugar _ _ -> recurseTerm desugar decl -- handled by coalesce*


desugarDeclType :: Bool -> Annotated Initial DeclType -> Praxis (Annotated Parse DeclType)
desugarDeclType recursive (a@(src, _) :< decl) = (a :<) <$> case decl of

  DeclTypeDataSugar optMode name args alts -> do
    args <- traverse desugar args
    alts <- traverse desugar alts
    let mode = case optMode of { Nothing -> if recursive then DataBoxed else DataUnboxed; Just mode -> mode }
    when (recursive && mode == DataUnboxed) $ throwAt Parse src $ "recursive datatype " <> pretty name <> " can not be unboxed"
    return (DeclTypeData mode name args alts)

  DeclTypeEnum name _
    | recursive -> throwAt Parse src $ "enum " <> pretty name <> " can not be recursive"
    | otherwise -> recurseTerm desugar decl


coalesceDeclTerms :: [Annotated s DeclTerm] -> Praxis [Annotated s DeclTerm]
coalesceDeclTerms [] = return []
coalesceDeclTerms (decl:decls) = case decl of
  (a1@(src, _) :< DeclTermSigSugar name1 sig) -> case decls of
    ((a2 :< DeclTermVar name2 _ exp):decls) | name1 == name2 -> do
      let decl = (a1 <> a2) :< DeclTermVar name2 (Just sig) exp
      decls <- coalesceDeclTerms decls
      return (decl:decls)
    _ -> throwAt Parse src $ "declaration of " <> pretty name1 <> " lacks an accompanying binding"
  _ -> (decl:) <$> coalesceDeclTerms decls

spanMaybe :: (a -> Maybe b) -> [a] -> ([b], [a])
spanMaybe _ [] = ([], [])
spanMaybe f (x:xs) = case f x of
  Just y  -> let (ys', xs') = spanMaybe f xs in (y:ys', xs')
  Nothing -> ([], xs)

coalesceDeclRecs :: [Annotated s DeclRec] -> Praxis [Annotated s DeclRec]
coalesceDeclRecs [] = return []
coalesceDeclRecs decls@((_ :< DeclRecTerm _) : _) = do
  let (declTerms, declOthers) = spanMaybe (\(_ :< decl) -> case decl of { DeclRecTerm decl -> Just decl; _ -> Nothing }) decls
  declTerms <- map (\declTerm@(a :< _) -> (a :< DeclRecTerm declTerm)) <$> coalesceDeclTerms declTerms
  declOthers <- coalesceDeclRecs declOthers
  return $ declTerms ++ declOthers
coalesceDeclRecs (decl:decls) = (decl:) <$> coalesceDeclRecs decls

coalesceDecls :: [Annotated s Decl] -> Praxis [Annotated s Decl]
coalesceDecls [] = return []
coalesceDecls decls@((_ :< DeclTerm _) : _) = do
  let (declTerms, declOthers) = spanMaybe (\(_ :< decl) -> case decl of { DeclTerm decl -> Just decl; _ -> Nothing }) decls
  declTerms <- map (\declTerm@(a :< _) -> (a :< DeclTerm declTerm)) <$> coalesceDeclTerms declTerms
  declOthers <- coalesceDecls declOthers
  return $ declTerms ++ declOthers
coalesceDecls (decl:decls) = (decl:) <$> coalesceDecls decls


-- TODO check for overlapping patterns?
desugarPat :: Annotated Initial Pat -> Praxis (Annotated Parse Pat)
desugarPat (a :< pat) = case pat of

  PatEnum "True"  -> pure (a :< PatLit (Bool True))

  PatEnum "False" -> pure (a :< PatLit (Bool False))

  _               -> (a :<) <$> recurseTerm desugar pat


desugarType :: Annotated Initial Type -> Praxis (Annotated Parse Type)
desugarType (a :< ty) = case ty of

  -- TODO allow more generic type synonyms
  TypeCon name -> do
    syn <- (parseState . typeSynonyms) `uses` Map.lookup name
    return $ case syn of
      Just ty -> ty
      Nothing -> a :< TypeCon name

  _           -> (a :<) <$> recurseTerm desugar ty


-- (Operator precedence) graph helpers

-- Repeatedly remove vertices with no outgoing edges, if we succeed the graph is acyclic
isAcyclic :: Graph -> Bool
isAcyclic g = isAcyclic' (map fst (assocs g)) where
  isAcyclic' [] = True
  isAcyclic' ns = if null leaves then False else isAcyclic' (ns \\ leaves) where
    leaves = filter (\n -> null (g ! n `intersect` ns)) ns

registerOp :: Source -> Annotated Parse Op -> (Name, Fixity) -> [Annotated Parse Prec] -> Praxis ()
registerOp src op (name, fixity) precs = do

    -- definition
    opDefinitions <- use (parseState . opState . definitions)
    when (op `Map.member` opDefinitions) $ throwAt Parse src ("operator already defined" :: String)
    parseState . opState . definitions %= Map.insert op (name, fixity)

    -- node
    case filter (\(_ :< Prec ord _) -> ord == EQ) precs of
      [] -> do
        parseState . opState . nodes %= (++ [[op]])
        parseState . opState . precedence %= \graph -> let n = length (vertices graph) in array (0, n) ((n, []) : assocs graph)
      [_ :< Prec _ refOp] ->
        parseState . opState . nodes %= map (\ops -> if refOp `elem` ops then op : ops else ops)
      _ ->
        throwAt Parse src $ "more than one equal precedence specified for op " <> pretty op

    -- edges (precedence relations)
    opNodes <- use (parseState . opState . nodes)
    let
      nodeToIndex = Map.fromList [ (op, i) | (i, ops) <- zip [0..] opNodes, op <- ops ]
      indexToNode = Map.fromList $ zip [0..] opNodes

    let
      edges =
        [ (op, refOp) | (_ :< Prec LT refOp) <- precs ] ++
        [ (refOp, op) | (_ :< Prec GT refOp) <- precs ]

      addEdge :: (Annotated Parse Op, Annotated Parse Op) -> Graph -> Graph
      addEdge (a, b) graph =
        let
          (a', b') = (nodeToIndex Map.! a, nodeToIndex Map.! b)
        in
          graph // [(a', nub (b' : graph ! a'))]

    traverse (\edge -> parseState . opState . precedence %= addEdge edge) edges

    -- check precedence is acyclic
    opPrecedence <- use (parseState . opState . precedence)
    unless (isAcyclic opPrecedence) $ throwAt Parse src ("operator precedence forms a cycle" :: String)

    return ()
