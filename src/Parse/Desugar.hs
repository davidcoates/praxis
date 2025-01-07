{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE OverloadedStrings      #-}

module Parse.Desugar
  ( run
  ) where

import           Common
import           Introspect
import qualified Parse.Mixfix        as Mixfix
import           Parse.State
import           Praxis
import           Print
import           Term

import           Control.Applicative (liftA3)
import           Control.Arrow       (left)
import           Control.Monad       (unless)
import           Data.Array          (array, assocs, bounds, elems, indices,
                                      listArray, (!), (//))
import           Data.Graph          (Graph, reachable)
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


run :: Term a => Annotated a -> Praxis (Annotated a)
run term = do
  term <- desugar term
  display "desugared term" term `ifFlag` debug
  return term

desugar :: Term a => Annotated a -> Praxis (Annotated a)
desugar term = ($ term) $ case typeof (view value term) of
  IBind           -> auto
  IDataCon        -> auto
  IExp            -> desugarExp
  IOp             -> desugarOp
  IPat            -> desugarPat
  IProgram        -> desugarProgram
  IType           -> desugarType
  IKind           -> auto
  IQType          -> auto
  ITypePat        -> auto
  ITypeConstraint -> auto
  ty              -> error (show ty)
  where
    auto :: Term a => Annotated a -> Praxis (Annotated a)
    auto = value (recurseTerm desugar)


desugarProgram :: Annotated Program -> Praxis (Annotated Program)
desugarProgram (a :< Program decls) = do
  decls <- (catMaybes <$> traverse desugarDecl decls) >>= coalesceDecls
  return (a :< Program decls)

collectFreeVars :: Annotated Exp -> Set Name
collectFreeVars x = collectFreeVars' x where
  collectFreeVars' :: Term a => Annotated a -> Set Name
  collectFreeVars' (_ :< x) = case typeof x of
    IExp -> case x of
      Var n -> Set.singleton n
      _     -> continue
    IDeclTerm -> case x of
      DeclTermVar n _ e -> Set.delete n (collectFreeVars' e)
      _                 -> continue
    _     -> continue
    where continue = getConst $ recurseTerm (Const . collectFreeVars') x


-- Helper for desugaring "&". It turns top-level VarRefSugar into Var and returns the name of such variables
desugarExpRef :: Annotated Exp -> Praxis (Annotated Exp, Set Name)
desugarExpRef (a :< exp) = case exp of

  Sig exp ty -> do
    (exp, readVars) <- desugarExpRef exp
    return (a :< Sig exp ty, readVars)

  Pair exp1 exp2 -> do
    (exp1, readVars1) <- desugarExpRef exp1
    (exp2, readVars2) <- desugarExpRef exp2
    return (a :< Pair exp1 exp2, readVars1 `Set.union` readVars2)

  VarRefSugar var -> return (a :< Var var, Set.singleton var)

  _ -> do
    exp <- desugarExp (a :< exp)
    return (exp, Set.empty)


desugarExp :: Annotated Exp -> Praxis (Annotated Exp)
desugarExp (a@(src, _) :< exp) = case exp of

  Apply f x -> do
    f <- desugarExp f
    let freeVars = collectFreeVars x
    (x, readVars) <- desugarExpRef x
    let mixedVars = freeVars `Set.intersection` readVars
    when (not (null mixedVars)) $ throwAt src $ "variable(s) " <> separate ", " (map pretty (Set.elems mixedVars)) <> " used in a read context"
    let unrollReads []     = (a :< Apply f x)
        unrollReads (v:vs) = (a :< Read v (unrollReads vs))
    return (unrollReads (Set.elems readVars))

  DoSugar stmts -> desugarStmts stmts where
    desugarStmts :: [Annotated Stmt] -> Praxis (Annotated Exp)
    desugarStmts [stmt]
      | (_ :< StmtExp exp)   <- stmt = desugarExp exp
      | (_ :< StmtBind bind) <- stmt = throwAt (view source stmt) ("do block must end in an expression" :: String)
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

  VarRefSugar var -> throwAt src $ "observed variable " <> pretty var <> " is not in a valid read context"

  Con "True" -> pure (a :< Lit (Bool True))

  Con "False" -> pure (a :< Lit (Bool False))

  Where exp decls -> do
    exp <- desugarExp exp
    decls <- traverse (desugarDeclTerm False) decls >>= coalesceDeclTerms
    return (a :< Where exp decls)

  _           -> (a :<) <$> recurseTerm desugar exp


desugarOp :: Annotated Op -> Praxis (Annotated Op)
desugarOp op@((src, _) :< Op parts) = do

  let hasConsecutiveHoles :: [Maybe Name] -> Bool
      hasConsecutiveHoles = \case
        (Nothing:Nothing:ps) -> True
        []                   -> False
        (p:ps)               -> hasConsecutiveHoles ps

  when (hasConsecutiveHoles parts) $ throwAt src $ "op " <> pretty op <> " has two consecutive holes"
  return op


desugarOpRules :: Annotated Op -> Annotated OpRules -> Praxis (Annotated OpRules)
desugarOpRules op (a@(src, _) :< OpRulesSugar rules) = do

    -- FIXME check the precedence operators exist?

    let assocs = mapMaybe (\r -> case r of { Left a -> Just a; _ -> Nothing}) rules
        precs  = mapMaybe (\r -> case r of {Right p -> Just p; _ -> Nothing}) rules

    when (length assocs > 1) $ throwAt src ("more than one associativity specified for op " <> pretty op)
    when (length  precs > 1) $ throwAt src ("more than one precedence block specified for op " <> pretty op)

    return (a :< OpRules (listToMaybe assocs) (concat precs))


desugarDecl :: Annotated Decl -> Praxis (Maybe (Annotated Decl))
desugarDecl (a@(src, _) :< decl) = case decl of

  DeclOpSugar op name rules -> do

    op@(_ :< Op parts) <- desugarOp op
    rules@(_ :< OpRules assoc precs) <- desugarOpRules op rules

    -- For simplicity of managing the op table, allow only one equal precedence relation
    let (eqPrecs, precs') = partition (\(_ :< Prec ord _) -> ord == EQ) precs
    unless (length eqPrecs <= 1) $ throwAt src ("more than one equal precedence specified for op " <> pretty op)
    let eq = listToMaybe eqPrecs

    -- Add operator to levels
    opLevels <- use (parseState . opContext . levels)
    let opLevels' = case eq of Nothing                 -> opLevels ++ [[view value op]]
                               Just (_ :< Prec EQ op') -> map (\ops -> if op' `elem` ops then view value op : ops else ops) opLevels

    let levelOf = Map.fromList (zip [0..] opLevels')
        indexOf = Map.fromList [ (op, i) | (i, ops) <- zip [0..] opLevels', op <- ops ]

    -- Determine fixity
    let noAssoc = unless (isNothing assoc) $ throwAt src ("associativity can not be specified for non-infix op " <> pretty op)
    fixity <- case (head parts, last parts) of
      (Nothing, Nothing) -> return (Infix (view value <$> assoc))
      (Nothing,  Just _) -> noAssoc >> return Postfix
      (Just _,  Nothing) -> noAssoc >> return Prefix
      (Just _,   Just _) -> noAssoc >> return Closed

    -- Add operator to definitions
    opDefns <- use (parseState . opContext . defns)
    when (view value op `Map.member` opDefns) $ throwAt src ("operator already defined" :: String)
    let opDefns' = Map.insert (view value op) (name, fixity) opDefns

    -- Add operator to precedence graph
    opPrec <- use (parseState . opContext . prec)
    let opPrec' = addOp (view value op) (map (view value) precs') indexOf opPrec
    unless (isAcyclic opPrec') $ throwAt src ("operator precedence forms a cycle" :: String)

    parseState . opContext .= OpContext { _defns = opDefns', _levels = opLevels', _prec = opPrec' }

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


desugarDeclRec :: Annotated DeclRec -> Praxis (Annotated DeclRec)
desugarDeclRec (a@(src, _) :< decl) = (a :<) <$> case decl of

  DeclRecTerm decl -> DeclRecTerm <$> desugarDeclTerm True decl

  DeclRecType decl -> DeclRecType <$> desugarDeclType True decl


expIsFunction :: Annotated Exp -> Bool
expIsFunction (_ :< exp) = case exp of
  Lambda _ _ -> True
  Cases  _   -> True
  _          -> False


desugarDeclTerm :: Bool -> Annotated DeclTerm -> Praxis (Annotated DeclTerm)
desugarDeclTerm recursive (a@(src, _) :< decl) = (a :<) <$> case decl of

  DeclTermDefSugar name args exp -> do
    args <- mapM desugarPat args
    let
      curry :: [Annotated Pat] -> Annotated Exp -> Annotated Exp
      curry []     e = e
      curry (p:ps) e = (view source p <> view source e, Nothing) :< Lambda p (curry ps e)
    exp <- curry args <$> desugarExp exp
    when (recursive && not (expIsFunction exp)) $ throwAt src $ "non-function " <> pretty name <> " can not be recursive"
    return $ DeclTermVar name Nothing exp

  DeclTermSigSugar _ _ -> recurseTerm desugar decl -- handled by coalesce*


desugarDeclType :: Bool -> Annotated DeclType -> Praxis (Annotated DeclType)
desugarDeclType recursive (a@(src, _) :< decl) = (a :<) <$> case decl of

  DeclTypeDataSugar optMode name args alts -> do
    args <- traverse desugar args
    alts <- traverse desugar alts
    let mode = case optMode of { Nothing -> if recursive then DataBoxed else DataUnboxed; Just mode -> mode }
    when (recursive && mode == DataUnboxed) $ throwAt src $ "recursive datatype " <> pretty name <> " can not be unboxed"
    return (DeclTypeData mode name args alts)

  DeclTypeEnum name _
    | recursive -> throwAt src $ "enum " <> pretty name <> " can not be recursive"
    | otherwise -> recurseTerm desugar decl


coalesceDeclTerms :: [Annotated DeclTerm] -> Praxis [Annotated DeclTerm]
coalesceDeclTerms [] = return []
coalesceDeclTerms (decl:decls) = case decl of
  (a1@(src, _) :< DeclTermSigSugar name1 sig) -> case decls of
    ((a2 :< DeclTermVar name2 _ exp):decls) | name1 == name2 -> do
      let decl = (a1 <> a2) :< DeclTermVar name2 (Just sig) exp
      decls <- coalesceDeclTerms decls
      return (decl:decls)
    _ -> throwAt src $ "declaration of " <> pretty name1 <> " lacks an accompanying binding"
  _ -> (decl:) <$> coalesceDeclTerms decls

spanMaybe :: (a -> Maybe b) -> [a] -> ([b], [a])
spanMaybe _ [] = ([], [])
spanMaybe f (x:xs) = case f x of
  Just y  -> let (ys', xs') = spanMaybe f xs in (y:ys', xs')
  Nothing -> ([], xs)

coalesceDeclRecs :: [Annotated DeclRec] -> Praxis [Annotated DeclRec]
coalesceDeclRecs [] = return []
coalesceDeclRecs decls@((_ :< DeclRecTerm _) : _) = do
  let (declTerms, declOthers) = spanMaybe (\(_ :< decl) -> case decl of { DeclRecTerm decl -> Just decl; _ -> Nothing }) decls
  declTerms <- map (\declTerm@(a :< _) -> (a :< DeclRecTerm declTerm)) <$> coalesceDeclTerms declTerms
  declOthers <- coalesceDeclRecs declOthers
  return $ declTerms ++ declOthers
coalesceDeclRecs (decl:decls) = (decl:) <$> coalesceDeclRecs decls

coalesceDecls :: [Annotated Decl] -> Praxis [Annotated Decl]
coalesceDecls [] = return []
coalesceDecls decls@((_ :< DeclTerm _) : _) = do
  let (declTerms, declOthers) = spanMaybe (\(_ :< decl) -> case decl of { DeclTerm decl -> Just decl; _ -> Nothing }) decls
  declTerms <- map (\declTerm@(a :< _) -> (a :< DeclTerm declTerm)) <$> coalesceDeclTerms declTerms
  declOthers <- coalesceDecls declOthers
  return $ declTerms ++ declOthers
coalesceDecls (decl:decls) = (decl:) <$> coalesceDecls decls


-- TODO check for overlapping patterns?
desugarPat :: Annotated Pat -> Praxis (Annotated Pat)
desugarPat (a :< pat) = case pat of

  PatEnum "True"  -> pure (a :< PatLit (Bool True))

  PatEnum "False" -> pure (a :< PatLit (Bool False))

  _               -> (a :<) <$> recurseTerm desugar pat


desugarType :: Annotated Type -> Praxis (Annotated Type)
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

addVertex :: Op -> Int -> Graph -> Graph
addVertex op n g = if n `elem` indices g then g else array (0, n) ((n, []) : assocs g)

addEdges :: [(Int, Int)] -> Graph -> Graph
addEdges []     g = g
addEdges (e:es) g = addEdges es (addEdge e g)

addEdge :: (Int, Int) -> Graph -> Graph
addEdge (a, b) g = g // [(a, nub (b : g ! a))]

addOp :: Op -> [Prec] -> Map Op Int -> Graph -> Graph
addOp op ps indexOf prec = addEdges (map edge ps) (addVertex op (indexOf Map.! op) prec) where
  edge (Prec LT gt) = (indexOf Map.! op, indexOf Map.! gt)
  edge (Prec GT lt) = (indexOf Map.! lt, indexOf Map.! op)
