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
import           Praxis
import           Pretty
import           Print
import           Record                 (Record, pair)
import qualified Record                 (fromList, toList)
import           Stage
import           Term

import           Control.Applicative    (liftA3)
import           Control.Arrow          (left)
import           Control.Monad          (unless)
import           Data.List              (intersperse, nub, partition)
import           Data.List              (intersect, (\\))
import           Data.Map.Strict        (Map)
import qualified Data.Map.Strict        as Map
import           Data.Maybe             (fromJust)
import           Data.Maybe             (catMaybes, isNothing, listToMaybe,
                                         mapMaybe)
import           Data.Monoid            ((<>))
import           Prelude                hiding (exp)
import           Text.Earley
import           Text.Earley.Mixfix.DAG (DAG)
import qualified Text.Earley.Mixfix.DAG as DAG

run :: Recursive a => Annotated a -> Praxis (Annotated a)
run x = save stage $ do
  stage .= Desugar
  x' <- desugar x
  display x' `ifFlag` debug
  return x'

desugar :: forall a. Recursive a => Annotated a -> Praxis (Annotated a)
desugar x = ($ x) $ case witness :: I a of
  IProgram -> program
  IExp     -> exp
  IPat     -> pat
  IType    -> ty
  IKind    -> pure
  ITyOp    -> pure

program :: Annotated Program -> Praxis (Annotated Program)
program (a :< Program ds) = do
  ds <- decls ds
  return (a :< Program ds)

stmts :: [Annotated Stmt] -> Praxis [Annotated Stmt]
stmts     [] = pure []
stmts (s:ss) | a :< StmtExp e <- s = do
                e' <- exp e
                ss' <- stmts ss
                return (a :< StmtExp e' : ss')
             | otherwise = do
                let (ds, rs) = span isStmtDecl (s:ss)
                ds' <- decls (map (\(_ :< StmtDecl d) -> d) ds)
                rs' <- stmts rs
                return $ map (\(a :< d) -> a :< StmtDecl (a :< d)) ds' ++ rs'
                  where isStmtDecl (_ :< StmtDecl _) = True
                        isStmtDecl _                 = False

record :: Source -> (Record b -> b) -> (a -> Praxis b) -> Record a -> Praxis b
record s build f r = do
  r' <- traverse f r
  case Record.toList r' of
    [(Nothing, x)] -> return $ x
    [(Just _, _)]  -> throwAt s ("illegal single-field record" :: String)
    _              -> return $ build r'

-- TODO clean up this 'fst a' nonsense
exp :: Annotated Exp -> Praxis (Annotated Exp)
exp (a :< x) = case x of

  Apply x (a' :< VarBang s) ->
    exp (a :< Read s (a :< Apply x (a' :< Var s))) -- TODO sources

  Do ss       -> do
    ss' <- stmts ss
    return (a :< Do ss')

  Mixfix ts   -> mixfix ts

  Record r    -> record (fst a) (\r' -> a :< Record r') exp r

  VarBang s   -> throwAt (fst a) $ "observed variable " <> quote (pretty s) <> " is not the argument of a function"

  _           -> (a :<) <$> recurse desugar x



operator :: Annotated Op -> Praxis (Annotated Op)
operator op@(a :< Op ns) = do

  let alternating :: [Bool] -> Bool
      alternating []     = True
      alternating (x:xs) = alternating' x xs
      alternating' :: Bool -> [Bool] -> Bool
      alternating' _ []      = True
      alternating' x (x':xs) = x /= x' && alternating' x' xs

  unless (alternating (map isNothing ns)) $ throwAt (fst a) $ "op " <> quote (pretty op) <> " is non-alternating holes"
  return op


opRules :: Annotated Op -> Annotated OpRules -> Praxis (Annotated OpRules)
opRules op (a :< OpMultiRules rs) = do

    -- FIXME check the precedence operators exist?

    let as = mapMaybe (\x -> case x of {Left a -> Just a; _ -> Nothing}) rs
        ps = mapMaybe (\x -> case x of {Right p -> Just p; _ -> Nothing}) rs

    when (length as > 1) $ throwAt (fst a) ("more than one associativity specified for op " <> quote (pretty op))
    when (length ps > 1) $ throwAt (fst a) ("more than one precedence block specified for op " <> quote (pretty op))

    return (a :< OpRules (listToMaybe as) (concat ps))


decls :: [Annotated Decl] -> Praxis [Annotated Decl]
decls []            = pure []
decls (a :< d : ds) = case d of

  DeclData n t as -> do
    t' <- traverse tyPat t
    as' <- traverse dataAlt as
    ds' <- decls ds
    return (a :< DeclData n t' as' : ds')

  DeclSig n t -> do
    t <- qty t
    decls ds >>= \case
      (a' :< DeclVar m Nothing e) : ds | m == n -> return $ ((a <> a') :< DeclVar n (Just t) e) : ds
      _                                         -> throwAt (fst a) $ "declaration of " <> quote (pretty n) <> " lacks an accompanying binding"

  DeclFun n ps e -> do
    ps <- mapM pat ps
    e  <- exp e
    let d = a :< DeclVar n Nothing (lambda ps e)
        lambda :: [Annotated Pat] -> Annotated Exp -> Annotated Exp
        lambda     [] e = e
        lambda (p:ps) e = (fst a, Nothing) :< Lambda p (lambda ps e)
    decls ds >>= \case
      []                                       -> return $ [d]
      (a' :< DeclVar m t as) : ds' | m == n    -> throwAt (fst a) $ "multiple definitions for " <> quote (pretty m)
      ds                                       -> return $ d:ds

  DeclOp op n rs -> do

    op <- operator op
    rs' <- opRules op rs

    let OpRules assoc ps = view value rs'

    -- For simplicity of managing the op table, allow only one equal precedence relation
    let (eqPrecs, ps') = partition (\(_ :< Prec ord _) -> ord == EQ) ps
    unless (length eqPrecs <= 1) $ throwAt (fst a) ("more than one equal precedence specified for op " <> quote (pretty op))
    let eq = listToMaybe eqPrecs

    -- Add operator to levels
    opLevels <- use (opContext . levels)
    let opLevels' = case eq of Nothing                 -> [view value op] : opLevels
                               Just (_ :< Prec EQ op') -> map (\ops -> if op' `elem` ops then view value op : ops else ops) opLevels

    -- Determine fixity and associativity
    let assoc' = case assoc of Nothing                -> DAG.NonAssoc
                               Just (_ :< AssocLeft)  -> DAG.LeftAssoc
                               Just (_ :< AssocRight) -> DAG.RightAssoc
        noAssoc :: Praxis ()
        noAssoc = unless (isNothing assoc) $ throwAt (fst a) ("associativity can not be specified for non-infix op " <> quote (pretty op))

        Op ns = view value op

    fixity <- case (head ns, last ns) of (Nothing, Nothing) -> return (DAG.Infix assoc')
                                         (Nothing,  Just _) -> noAssoc >> return DAG.Postfix
                                         (Just _,  Nothing) -> noAssoc >> return DAG.Prefix
                                         (Just _,   Just _) -> noAssoc >> return DAG.Closed

    -- Add operator to table
    opTable <- use (opContext . table)
    when (view value op `Map.member` opTable) $ throwAt (fst a) ("operator already defined" :: String)
    let opTable' = Map.insert (view value op) (n, fixity, ps') opTable

    let opGraph = makeOpGraph opLevels' opTable'
    unless (acyclic opGraph) $ throwAt (fst a) ("operator precedence forms a cycle" :: String)

    let showOpGraph = display . unlines $ map showOp (DAG.nodes opGraph)
        showOp n = unlines $ [show n] ++ map showOpNode (DAG.value opGraph n) ++ map show (DAG.neighbors opGraph n)
        showOpNode :: OpNode -> String
        showOpNode op = unwords (map (show . view value) (DAG.parts op)) ++ " " ++ show (DAG.fixity op)

    showOpGraph `ifFlag` debug

    opContext .= OpContext { _table = opTable', _levels = opLevels', _graph = opGraph }

    ds' <- decls ds
    return (a :< DeclOp op n rs' : ds')


dataAlt :: Annotated DataAlt -> Praxis (Annotated DataAlt)
dataAlt (a :< x) = (a :<) <$> case x of

  DataAlt n ts ->  DataAlt n <$> traverse ty ts


-- TODO check for overlapping patterns?
pat :: Annotated Pat -> Praxis (Annotated Pat)
pat (a :< x) = case x of

  PatRecord r -> record (fst a) (\r' -> a :< PatRecord r') pat r

  _           -> (a :<) <$> recurse desugar x


ty :: Annotated Type -> Praxis (Annotated Type)
ty (a :< x) = case x of

  TyRecord r -> record (fst a) (\r' -> a :< TyRecord r') ty r

  _          -> (a :<) <$> recurse desugar x


qty :: Annotated QType -> Praxis (Annotated QType)
qty (a :< x) = (a :<) <$> case x of

  Mono t      -> Mono <$> ty t

  Forall vs t -> Forall vs <$> ty t


tyPat :: Annotated TyPat -> Praxis (Annotated TyPat)
tyPat (a :< x) = (a :<) <$> recurse desugar x


type MTok = DAG.Tok (Annotated Name) (Annotated Exp)

tok :: Annotated Tok -> Praxis MTok
tok (a :< TOp op) = pure (DAG.TOp (a :< op))
tok (a :< TExp e) = DAG.TExpr <$> exp e

mixfix :: [Annotated Tok] -> Praxis (Annotated Exp)
mixfix ts = do
  let s = view source (head ts)
  ts' <- mapM tok ts
  opGraph <- use (opContext . graph)
  let (parses, _) = fullParses (parser (DAG.simpleMixfixExpression opGraph)) ts'
  case parses of [e] -> return e
                 []  -> throwAt s ("no mixfix parse" :: String) -- TODO more info
                 _   -> throwAt s ("ambiguous mixfix parse" :: String) -- TODO more info


makeOpGraph :: [[Op]] -> OpTable -> OpGraph
makeOpGraph ls opTable = DAG.DAG { DAG.nodes = map fst ils, DAG.neighbors = neighbours, DAG.value = (\i -> map valueOf (levelOf i)) } where

    ils = zip [1..] ls

    indexOf :: Op -> Int
    indexOf op = indexOf' ils where
      indexOf' ((i,ops):ils) = if op `elem` ops then i else indexOf' ils

    levelOf :: Int -> [Op]
    levelOf i = levelOf' ils where
      levelOf' ((j,ops):ils) = if i == j then ops else levelOf' ils

    equiv :: Op -> [Op]
    equiv op = equiv' ils where
      equiv' ((_,ops):ils) = if op `elem` ops then ops else equiv' ils

    directNeighbours :: Op -> [Op]
    directNeighbours op = explicit ++ implicit where
      explicit = [ op' | (_ :< Prec LT op') <- (\(_, _, ps) -> ps) (opTable Map.! op) ]
      implicit = [ op' | (op', (_, _, ps)) <- Map.toList opTable, (_ :< Prec GT op'') <- ps, op'' == op ]

    neighbours :: Int -> [Int]
    neighbours i = nub . concat . map neighbours' $ levelOf i
    neighbours' :: Op -> [Int]
    neighbours' op = map indexOf (concat (map equiv (directNeighbours op)))

    valueOf :: Op -> OpNode
    valueOf op@(Op parts) = DAG.Op { DAG.parts = map phantom (catMaybes parts), DAG.build = build, DAG.fixity = fix } where
      (n, fix, _) = opTable Map.! op
      -- FIXME combine annotations
      build :: [Annotated Exp] -> Annotated Exp
      build ps = phantom $ Apply (phantom $ Var n) (phantom $ Record (Record.fromList (zip (repeat Nothing) ps)))


-- Repeatedly remove vertices with no outgoing edges, if we succeed the graph is acyclic
acyclic :: Eq a => DAG a b -> Bool
acyclic g = acyclic' (DAG.nodes g) where
  acyclic' [] = True
  acyclic' ns = if null leaves then False else acyclic' (ns \\ leaves) where
    leaves = filter (\n -> null (DAG.neighbors g n `intersect` ns)) ns

