{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE OverloadedStrings      #-}
{-# LANGUAGE ScopedTypeVariables    #-}

module Parse.Desugar
  ( run
  ) where

import           Common
import           Env
import           Introspect
import qualified Parse.Mixfix        as Mixfix
import           Praxis
import           Print
import           Stage
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
run term = save stage $ do
  stage .= Desugar
  term <- desugar term
  term <- rewrite term
  display term `ifFlag` debug
  return term

desugar :: forall a. Term a => Annotated a -> Praxis (Annotated a)
desugar term = ($ term) $ case witness :: I a of
  IProgram -> desugarProgram
  IExp     -> desugarExp
  IPat     -> desugarPat
  IType    -> desugarTy
  IOp      -> desugarOp
  IOpRules -> error "standalone IOpRules"
  IDecl    -> error "standalone Decl"
  _        -> value (recurse desugar)


-- Term rewriting. This is used to rewrite type-level variables to guarantee uniqueness which is needed for the solver.
-- The rewrite mapping is stored so it can be applied in reverse when displaying diagnostics to the user.

rewrite :: forall a. Term a => Annotated a -> Praxis (Annotated a)
rewrite term = ($ term) $ case witness :: I a of
  IDecl  -> rewriteDecl
  IQType -> rewriteQType -- for standalone QTypes (used in tests)
  _      -> value (recurse rewrite)

qTyVarNames :: [Annotated QTyVar] -> [Name]
qTyVarNames vs = [ n | QTyVar n <- map (view value) vs ]

qTyVarOpNames :: [Annotated QTyVar] -> [Name]
qTyVarOpNames vs = [ n | QTyOpVar _ n <- map (view value) vs ]

-- Substitions are generated and applied in a piece-meal way (i.e. per declaration)
-- So we expect them to be individually fairly small, which is why we're just using assoc lists here rather than a Map.
data RewriteMap = RewriteMap { _tyVars :: [(Name, Name)], _tyOpVars :: [(Name, Name)] }

rewriteMapFromQType :: Annotated QType -> Praxis RewriteMap
rewriteMapFromQType ((src, _) :< Forall boundVars _ _) = do

  tyVars <-   series $ [ (\(_ :< TyVar m) -> (n, m)) <$> freshTyVar | n <- qTyVarNames boundVars ]
  tyOpVars <- series $ [ (\(_ :< TyOpVar _ m) -> (n, m)) <$> freshTyOpVar undefined | n <- qTyVarOpNames boundVars ]

  let allTyVars = tyVars ++ tyOpVars
      isUnique xs = length (nub xs) == length xs
  when (not (isUnique (map fst allTyVars))) $ throwAt src $ ("quantified type variables are not distinct" :: String)

  -- Map from generated name (freshTyVar / freshTyOpVar) to the original name
  tyVarMap %= Map.union (Map.fromList (map (\(a, b) -> (b, a)) allTyVars))

  return RewriteMap { _tyVars = tyVars, _tyOpVars = tyOpVars }


applyRewriteMap :: Term a => RewriteMap -> Annotated a -> Annotated a
applyRewriteMap RewriteMap { _tyVars = tyVars, _tyOpVars = tyOpVars } = sub $ \term -> case typeof term of
  IType   |     TyVar n   <- term ->      TyVar <$> n `Prelude.lookup` tyVars
  ITyOp   |   TyOpVar d n <- term ->  TyOpVar d <$> n `Prelude.lookup` tyOpVars
  IQTyVar |    QTyVar n   <- term ->     QTyVar <$> n `Prelude.lookup` tyVars
  IQTyVar |  QTyOpVar d n <- term -> QTyOpVar d <$> n `Prelude.lookup` tyOpVars
  _                               -> Nothing

rewriteQType :: Annotated QType -> Praxis (Annotated QType)
rewriteQType qTy = do
  rwMap <- rewriteMapFromQType qTy
  return (applyRewriteMap rwMap qTy)

rewriteDecl :: Annotated Decl -> Praxis (Annotated Decl)
rewriteDecl (ann@(src, _) :< decl) = case decl of

  DeclVar name sig exp -> do

    {-
    Type variables need to be renamed to be globally unqiue, because the type solver acts globally.

    E.g.
      foo : forall a. C a => a -> a
      foo = ... where
       bar : forall a. D a => a -> a
       bar x = (x : a)
    -->
      foo : forall a1. C a1 => a1 -> a1
      foo = ... where
        bar : forall a2. D a2 => a2 -> a2
        bar x = (x : a2)
    -}

    case sig of

      Nothing -> do -- Lack of type signature implies a monomorphic function, so just recurse
        value (recurse rewrite) (ann :< decl)

      Just sig -> do
        -- Recursiively rewrite first to handle nested declarations
        exp <- value (recurse rewrite) exp
        -- Now rewrite for the top level tyVars
        rwMap <- rewriteMapFromQType sig
        return (ann :< DeclVar name (Just (applyRewriteMap rwMap sig)) (applyRewriteMap rwMap exp))

  -- FIXME !!! As per above, type pattern variables (in DeclData) need to be renamed

  _ -> value (recurse rewrite) (ann :< decl)



-- Desugaring proper

desugarProgram :: Annotated Program -> Praxis (Annotated Program)
desugarProgram (ann :< Program decls) = do
  decls <- desugarDecls decls
  return (ann :< Program decls)

collectFreeVars :: Annotated Exp -> Set Name
collectFreeVars = extractPartial f where
  f :: forall a. Term a => a -> (Set Name, Bool)
  f x = case witness :: I a of
    IExp  -> case x of
      Var n -> (Set.singleton n, False)
      _     -> (Set.empty,        True)
    IDecl -> case x of
      DeclVar n _ e -> (Set.delete n (collectFreeVars e), False)
      _             -> (Set.empty,                         True)
    _     -> (Set.empty, True)

-- Helper for desugaring "&". It turns top-level VarRef into Var and returns the name of such variables
desugarExpRef :: Annotated Exp -> Praxis (Annotated Exp, Set Name)
desugarExpRef (ann :< exp) = case exp of

  Sig exp ty -> do
    (exp, readVars) <- desugarExpRef exp
    return (ann :< Sig exp ty, readVars)

  Pair exp1 exp2 -> do
    (exp1, readVars1) <- desugarExpRef exp1
    (exp2, readVars2) <- desugarExpRef exp2
    return (ann :< Pair exp1 exp2, readVars1 `Set.union` readVars2)

  VarRef var -> return (ann :< Var var, Set.singleton var)

  _ -> do
    exp <- desugar (ann :< exp)
    return (exp, Set.empty)


desugarExp :: Annotated Exp -> Praxis (Annotated Exp)
desugarExp (ann@(src, _) :< exp) = case exp of

  Apply f x -> do
    f <- desugar f
    let freeVars = collectFreeVars x
    (x, readVars) <- desugarExpRef x
    let mixedVars = freeVars `Set.intersection` readVars
    when (not (null mixedVars)) $ throwAt src $ "variable(s) " <> separate ", " (map (quote . pretty) (Set.elems mixedVars)) <> " used in a read context"
    let unrollReads []     = (ann :< Apply f x)
        unrollReads (v:vs) = (ann :< Read v (unrollReads vs))
    return (unrollReads (Set.elems readVars))

    -- Call Mixfix.parse to fold the token sequence into a single expression, then desugar that expression
  Mixfix tokens -> Mixfix.parse src tokens >>= desugar

  VarRef var -> throwAt src $ "observed variable " <> quote (pretty var) <> " is not in a valid read context"

  Con "True" -> pure (ann :< Lit (Bool True))

  Con "False" -> pure (ann :< Lit (Bool False))

  Where exp decls -> do
    exp <- desugar exp
    decls <- desugarDecls decls
    return (ann :< Where exp decls)

  _           -> (ann :<) <$> recurse desugar exp



desugarOp :: Annotated Op -> Praxis (Annotated Op)
desugarOp op@((src, _) :< Op parts) = do

  let hasConsecutiveHoles :: [Maybe Name] -> Bool
      hasConsecutiveHoles = \case
        (Nothing:Nothing:ps) -> True
        []                   -> False
        (p:ps)               -> hasConsecutiveHoles ps

  when (hasConsecutiveHoles parts) $ throwAt src $ "op " <> quote (pretty op) <> " has two consecutive holes"
  return op


desugarOpRules :: Annotated Op -> Annotated OpRules -> Praxis (Annotated OpRules)
desugarOpRules op (ann@(src, _) :< OpMultiRules rules) = do

    -- FIXME check the precedence operators exist?

    let assocs = mapMaybe (\r -> case r of { Left a -> Just a; _ -> Nothing}) rules
        precs  = mapMaybe (\r -> case r of {Right p -> Just p; _ -> Nothing}) rules

    when (length assocs > 1) $ throwAt src ("more than one associativity specified for op " <> quote (pretty op))
    when (length  precs > 1) $ throwAt src ("more than one precedence block specified for op " <> quote (pretty op))

    return (ann :< OpRules (listToMaybe assocs) (concat precs))


desugarDecls :: [Annotated Decl] -> Praxis [Annotated Decl]
desugarDecls []            = pure []
desugarDecls (ann@(src, _) :< decl : decls) = case decl of

  DeclData name ty args -> do
    ty <- traverse desugar ty
    args <- traverse desugar args
    decls <- desugarDecls decls
    return (ann :< DeclData name ty args : decls)

  DeclSig name ty -> do
    ty <- desugar ty
    desugarDecls decls >>= \case
      (ann' :< DeclVar name' Nothing exp) : decls
        | name == name' -> return $ ((ann <> ann') :< DeclVar name (Just ty) exp) : decls
      _ -> throwAt src $ "declaration of " <> quote (pretty name) <> " lacks an accompanying binding"

  DeclFun name args exp -> do
    args <- mapM desugar args
    exp <- desugar exp
    let decl = ann :< DeclVar name Nothing (curry args exp)
        curry :: [Annotated Pat] -> Annotated Exp -> Annotated Exp
        curry     [] e = e
        curry (p:ps) e = (src, Nothing) :< Lambda p (curry ps e)
    desugarDecls decls >>= \case
      [] -> return $ [decl]
      (_ :< DeclVar name' _ _) : _
        | name == name' -> throwAt src $ "multiple definitions for " <> quote (pretty name)
      decls -> return $ decl:decls

  DeclOp op name rules -> do

    op@(_ :< Op parts) <- desugar op
    rules@(_ :< OpRules assoc precs) <- desugarOpRules op rules

    -- For simplicity of managing the op table, allow only one equal precedence relation
    let (eqPrecs, precs') = partition (\(_ :< Prec ord _) -> ord == EQ) precs
    unless (length eqPrecs <= 1) $ throwAt src ("more than one equal precedence specified for op " <> quote (pretty op))
    let eq = listToMaybe eqPrecs

    -- Add operator to levels
    opLevels <- use (opContext . levels)
    let opLevels' = case eq of Nothing                 -> opLevels ++ [[view value op]]
                               Just (_ :< Prec EQ op') -> map (\ops -> if op' `elem` ops then view value op : ops else ops) opLevels

    let levelOf = Map.fromList (zip [0..] opLevels')
        indexOf = Map.fromList [ (op, i) | (i, ops) <- zip [0..] opLevels', op <- ops ]

    -- Determine fixity
    let noAssoc = unless (isNothing assoc) $ throwAt src ("associativity can not be specified for non-infix op " <> quote (pretty op))
    fixity <- case (head parts, last parts) of
      (Nothing, Nothing) -> return (Infix (view value <$> assoc))
      (Nothing,  Just _) -> noAssoc >> return Postfix
      (Just _,  Nothing) -> noAssoc >> return Prefix
      (Just _,   Just _) -> noAssoc >> return Closed

    -- Add operator to definitions
    opDefns <- use (opContext . defns)
    when (view value op `Map.member` opDefns) $ throwAt src ("operator already defined" :: String)
    let opDefns' = Map.insert (view value op) (name, fixity) opDefns

    -- Add operator to precedence graph
    opPrec <- use (opContext . prec)
    let opPrec' = addOp (view value op) (map (view value) precs') indexOf opPrec
    unless (isAcyclic opPrec') $ throwAt src ("operator precedence forms a cycle" :: String)

    opContext .= OpContext { _defns = opDefns', _levels = opLevels', _prec = opPrec' }

    decls <- desugarDecls decls
    return (ann :< DeclOp op name rules : decls)


  DeclSyn name ty -> do
    ty <- desugar ty
    tySynonyms %= Map.insert name ty
    decls <- desugarDecls decls
    return (ann :< DeclSyn name ty : decls)


-- TODO check for overlapping patterns?
desugarPat :: Annotated Pat -> Praxis (Annotated Pat)
desugarPat (ann :< pat) = case pat of

  PatCon "True" Nothing  -> pure (ann :< PatLit (Bool True))

  PatCon "False" Nothing -> pure (ann :< PatLit (Bool False))

  _                      -> (ann :<) <$> recurse desugar pat


desugarTy :: Annotated Type -> Praxis (Annotated Type)
desugarTy (ann :< ty) = case ty of

  -- TODO allow more generic type synonyms
  TyCon name -> do
    syn <- tySynonyms `uses` Map.lookup name
    return $ case syn of
      Just ty  -> ty
      Nothing  -> ann :< TyCon name

  _           -> (ann :<) <$> recurse desugar ty


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
