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
import           Introspect
import           Praxis
import           Pretty
import           Print
import           Record                 (Record, pair)
import qualified Record                 (toList)
import           Stage
import           Term

import           Control.Applicative    (liftA3)
import           Control.Arrow          (left)
import           Control.Monad          (unless)
import           Data.List              (intersperse)
import           Data.Map               (Map)
import qualified Data.Map               as Map
import           Data.Monoid            ((<>))
import           Prelude                hiding (exp)
import           Text.Earley
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


decls :: [Annotated Decl] -> Praxis [Annotated Decl]
decls []            = pure []
decls (a :< d : ds) = case d of

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
      (a' :< DeclVar m t as) : ds' | m == n    -> error "TODO multiple definitions"
      ds                                       -> return $ d:ds

  DeclData n t as -> do
    t' <- traverse tyPat t
    as' <- traverse dataAlt as
    ds' <- decls ds
    return (a :< DeclData n t' as' : ds')


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


type MTok = DAG.Tok (Tag (Source, Maybe Void) Op) (Annotated Exp)

tok :: Annotated Tok -> Praxis MTok
tok (a :< TOp op) = pure (DAG.TOp (a :< op))
tok (a :< TExp e) = DAG.TExpr <$> exp e

mixfix :: [Annotated Tok] -> Praxis (Annotated Exp)
mixfix ts = do
  ts' <- mapM tok ts
  -- TODO do something with report?
  let (parses, _) = fullParses (parser (DAG.simpleMixfixExpression opTable)) ts'
  case parses of [e] -> return e
                 _   -> error "TODO resolve error make a proper error for this (ambiguous mixfix parse)"

type OpTable = DAG.DAG Int [DAG.Op (Tag (Source, Maybe Void) Op) (Annotated Exp)]

-- TODO build this dynamically from bindings
-- FIXME source annotations not preserved!!!
opTable :: OpTable
opTable = DAG.DAG
  { DAG.nodes = [6, 7, 9]
  , DAG.neighbors = \case
      6 -> [7,9]
      7 -> [9]
      9 -> []
  , DAG.value = \case
      6 -> [ add, sub ]
      7 -> [ mul ]
      9 -> [ dot ]
  }
  where build a s n = DAG.Op { DAG.fixity = DAG.Infix a, DAG.parts = [phantom $ QString { qualification = [], name = s }], DAG.build = \[e1, e2] -> build' n e1 e2 }
        build' n e1 e2 = phantom $ Apply (phantom $ Var n) (phantom $ Record (pair e1 e2)) :: Annotated Exp -- TODO annotations?
        add = build DAG.LeftAssoc "+" "add"
        sub = build DAG.LeftAssoc "-" "sub"
        mul = build DAG.LeftAssoc "*" "mul"
        dot = build DAG.RightAssoc "." "dot"

