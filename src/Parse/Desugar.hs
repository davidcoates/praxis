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
run x = save stage $ do
  stage .= Desugar
  x <- desugar x
  x <- rewrite x
  display x `ifFlag` debug
  return x

desugar :: forall a. Term a => Annotated a -> Praxis (Annotated a)
desugar x = ($ x) $ case witness :: I a of
  IProgram -> program
  IExp     -> exp
  IPat     -> pat
  IType    -> ty
  IOp      -> operator
  IOpRules -> error "standalone IOpRules"
  IDecl    -> error "standalone Decl"
  _        -> value (recurse desugar)

rewrite :: forall a. Term a => Annotated a -> Praxis (Annotated a)
rewrite x = ($ x) $ case witness :: I a of
  IDecl  -> rewriteDecl
  IQType -> rewriteQType
  _      -> value (recurse rewrite)

qTyVarNames :: [Annotated QTyVar] -> [Name]
qTyVarNames vs = [ n | QTyVar n <- map (view value) vs ]

qTyVarOpNames :: [Annotated QTyVar] -> [Name]
qTyVarOpNames vs = [ n | QTyOpVar d n <- map (view value) vs ]

genTyVarMap :: Annotated QType -> Praxis ([(Name, Name)], [(Name, Name)])
genTyVarMap ((s, _) :< Forall vs cs t) = do

  vars <-   series $ [ (\(_ :< TyVar m) -> (n, m)) <$> freshTyVar | n <- qTyVarNames vs ]
  opVars <- series $ [ (\(_ :< TyOpVar _ m) -> (n, m)) <$> freshTyOpVar undefined | n <- qTyVarOpNames vs ]

  let all = vars ++ opVars
      unique xs = length (nub xs) == length xs
  when (not (unique (map fst all))) $ throwAt s $ ("quantified type variables are not distinct" :: String)

  -- Map from generated name (freshTyVar / freshTyOpVar) to the original name
  tyVarMap %= Map.union (Map.fromList (map (\(a, b) -> (b, a)) all))

  return (vars, opVars)


rewriteTyVars :: Term a => ([(Name, Name)], [(Name, Name)]) -> Annotated a -> Annotated a
rewriteTyVars (vars, opVars) = sub $ \x -> case typeof x of
  IType   |     TyVar n   <- x ->      TyVar <$> n `Prelude.lookup` vars
  ITyOp   |   TyOpVar d n <- x ->  TyOpVar d <$> n `Prelude.lookup` opVars
  IQTyVar |    QTyVar n   <- x ->     QTyVar <$> n `Prelude.lookup` vars
  IQTyVar |  QTyOpVar d n <- x -> QTyOpVar d <$> n `Prelude.lookup` opVars
  _                            -> Nothing


rewriteQType :: Annotated QType -> Praxis (Annotated QType)
rewriteQType t = do
  m <- genTyVarMap t
  return (rewriteTyVars m t)

rewriteDecl :: Annotated Decl -> Praxis (Annotated Decl)
rewriteDecl (a@(s, _) :< x) = case x of

  DeclVar n sig e -> do

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
        value (recurse rewrite) (a :< x)

      Just sig -> do
        -- Recursiively rewrite first to handle nested declarations
        e <- value (recurse rewrite) e
        -- Now rewrite for the top level tyVars
        m <- genTyVarMap sig
        return (a :< DeclVar n (Just (rewriteTyVars m sig)) (rewriteTyVars m e))

  -- FIXME !!! As per above, type pattern variables (in DeclData) need to be renamed

  _ -> value (recurse rewrite) (a :< x)



program :: Annotated Program -> Praxis (Annotated Program)
program (a :< Program ds) = do
  ds <- decls ds
  return (a :< Program ds)

freeVars :: Annotated Exp -> Set Name
freeVars = extractPartial f where
  f :: forall a. Term a => a -> (Set Name, Bool)
  f x = case witness :: I a of
    IExp  -> case x of
      Var n -> (Set.singleton n, False)
      _     -> (Set.empty,        True)
    IDecl -> case x of
      DeclVar n _ e -> (Set.delete n (freeVars e), False)
      _             -> (Set.empty,                  True)
    _     -> (Set.empty, True)

-- Helper for desugaring &
-- Turns top-level VarRef into Var and returns the name of such variables
expRead :: Annotated Exp -> Praxis (Annotated Exp, Set Name)
expRead (a :< x) = case x of

  Sig e t -> do
    (e', ns) <- expRead e
    return (a :< Sig e' t, ns)

  Pair x y -> do
    (x', ns) <- expRead x
    (y', ms) <- expRead y
    return (a :< Pair x' y', ns `Set.union` ms)

  VarRef n -> return (a :< Var n, Set.singleton n)

  _ -> do
    x' <- exp (a :< x)
    return (x', Set.empty)


exp :: Annotated Exp -> Praxis (Annotated Exp)
exp (a@(s, _) :< x) = case x of

  Apply x y -> do
    x' <- exp x
    (y', ns) <- expRead y
    let mixedVars = freeVars y `Set.intersection` ns
    when (not (null mixedVars)) $ throwAt s $ "variable(s) " <> separate ", " (map (quote . pretty) (Set.elems mixedVars)) <> " used in a read context"
    let unwrap []     = (a :< Apply x' y')
        unwrap (n:ns) = (a :< Read n (unwrap ns))
    return (unwrap (Set.elems ns))

  Mixfix ts   -> Mixfix.parse s ts >>= exp -- Need to desguar after parsing

  VarRef v    -> throwAt s $ "observed variable " <> quote (pretty v) <> " is not in a valid read context"

  Con "True"  -> pure (a :< Lit (Bool True))

  Con "False" -> pure (a :< Lit (Bool False))

  Where x ys -> do
    x' <- exp x
    ys' <- decls ys
    return (a :< Where x' ys')

  _           -> (a :<) <$> recurse desugar x



operator :: Annotated Op -> Praxis (Annotated Op)
operator op@(a@(s, _) :< Op ns) = do

  let consecutiveHoles :: [Maybe Name] -> Bool
      consecutiveHoles = \case
        (Nothing:Nothing:xs) -> True
        []                   -> False
        (x:xs)               -> consecutiveHoles xs

  when (consecutiveHoles ns) $ throwAt s $ "op " <> quote (pretty op) <> " has two consecutive holes"
  return op


opRules :: Annotated Op -> Annotated OpRules -> Praxis (Annotated OpRules)
opRules op (a@(s, _) :< OpMultiRules rs) = do

    -- FIXME check the precedence operators exist?

    let as = mapMaybe (\x -> case x of {Left a -> Just a; _ -> Nothing}) rs
        ps = mapMaybe (\x -> case x of {Right p -> Just p; _ -> Nothing}) rs

    when (length as > 1) $ throwAt s ("more than one associativity specified for op " <> quote (pretty op))
    when (length ps > 1) $ throwAt s ("more than one precedence block specified for op " <> quote (pretty op))

    return (a :< OpRules (listToMaybe as) (concat ps))


decls :: [Annotated Decl] -> Praxis [Annotated Decl]
decls []            = pure []
decls (a@(s, _) :< d : ds) = case d of

  DeclData n t as -> do
    t' <- traverse desugar t
    as' <- traverse desugar as
    ds' <- decls ds
    return (a :< DeclData n t' as' : ds')

  DeclSig n t -> do
    t <- desugar t
    decls ds >>= \case
      (a' :< DeclVar m Nothing e) : ds | m == n -> return $ ((a <> a') :< DeclVar n (Just t) e) : ds
      _                                         -> throwAt s $ "declaration of " <> quote (pretty n) <> " lacks an accompanying binding"

  DeclFun n ps e -> do
    ps <- mapM pat ps
    e  <- exp e
    let d = a :< DeclVar n Nothing (lambda ps e)
        lambda :: [Annotated Pat] -> Annotated Exp -> Annotated Exp
        lambda     [] e = e
        lambda (p:ps) e = (s, Nothing) :< Lambda p (lambda ps e)
    decls ds >>= \case
      []                                       -> return $ [d]
      (a' :< DeclVar m t as) : ds' | m == n    -> throwAt s $ "multiple definitions for " <> quote (pretty m)
      ds                                       -> return $ d:ds

  DeclOp op n rs -> do

    op <- desugar op
    rs' <- opRules op rs

    let OpRules assoc ps = view value rs'

    -- For simplicity of managing the op table, allow only one equal precedence relation
    let (eqPrecs, ps') = partition (\(_ :< Prec ord _) -> ord == EQ) ps
    unless (length eqPrecs <= 1) $ throwAt s ("more than one equal precedence specified for op " <> quote (pretty op))
    let eq = listToMaybe eqPrecs

    -- Add operator to levels
    opLevels <- use (opContext . levels)
    let opLevels' = case eq of Nothing                 -> opLevels ++ [[view value op]]
                               Just (_ :< Prec EQ op') -> map (\ops -> if op' `elem` ops then view value op : ops else ops) opLevels

    let levelOf = Map.fromList (zip [0..] opLevels')
        indexOf = Map.fromList [ (op, i) | (i, ops) <- zip [0..] opLevels', op <- ops ]

    -- Determine fixity
    let noAssoc = unless (isNothing assoc) $ throwAt s ("associativity can not be specified for non-infix op " <> quote (pretty op))
        Op ns = view value op
    fixity <- case (head ns, last ns) of
      (Nothing, Nothing) -> return (Infix (view value <$> assoc))
      (Nothing,  Just _) -> noAssoc >> return Postfix
      (Just _,  Nothing) -> noAssoc >> return Prefix
      (Just _,   Just _) -> noAssoc >> return Closed

    -- Add operator to definitions
    opDefns <- use (opContext . defns)
    when (view value op `Map.member` opDefns) $ throwAt s ("operator already defined" :: String)
    let opDefns' = Map.insert (view value op) (n, fixity) opDefns

    -- Add operator to precedence graph
    opPrec <- use (opContext . prec)
    let opPrec' = addOp (view value op) (map (view value) ps') indexOf opPrec
    unless (acyclic opPrec') $ throwAt s ("operator precedence forms a cycle" :: String)

    opContext .= OpContext { _defns = opDefns', _levels = opLevels', _prec = opPrec' }

    ds' <- decls ds
    return (a :< DeclOp op n rs' : ds')


  DeclSyn n t -> do
    t' <- ty t
    tySynonyms %= Map.insert n t'
    ds' <- decls ds
    return (a :< DeclSyn n t' : ds')


-- TODO check for overlapping patterns?
pat :: Annotated Pat -> Praxis (Annotated Pat)
pat (a :< x) = case x of

  PatCon "True" Nothing  -> pure (a :< PatLit (Bool True))

  PatCon "False" Nothing -> pure (a :< PatLit (Bool False))

  _                      -> (a :<) <$> recurse desugar x


ty :: Annotated Type -> Praxis (Annotated Type)
ty (a :< x) = case x of

  -- TODO allow more generic type synonyms
  TyCon n -> do
    syn <- tySynonyms `uses` Map.lookup n
    return $ case syn of
      Just t  -> t
      Nothing -> a :< TyCon n

  _           -> (a :<) <$> recurse desugar x


-- Repeatedly remove vertices with no outgoing edges, if we succeed the graph is acyclic
acyclic :: Graph -> Bool
acyclic g = acyclic' (map fst (assocs g)) where
  acyclic' [] = True
  acyclic' ns = if null leaves then False else acyclic' (ns \\ leaves) where
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
