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
import           Praxis
import           Print
import           Record                 (Record, pair)
import qualified Record                 (toList)
import           Term

import           Control.Applicative    (Const, liftA2, liftA3)
import           Control.Arrow          (left)
import           Control.Monad          (unless)
import           Data.List              (intersperse)
import           Data.Map               (Map)
import qualified Data.Map               as Map
import           Data.Monoid            ((<>))
import           Prelude                hiding (exp)
import           Text.Earley
import qualified Text.Earley.Mixfix.DAG as DAG

run :: Recursive a => Simple a -> Praxis (Simple a)
run x = save stage $ do
  stage .= Desugar
  x' <- desugar x
  output x'
  return x'

desugar :: Recursive a => Simple a -> Praxis (Simple a)
desugar x = ($ x) $ case typeof x of
  IProgram -> program
  IExp     -> exp
  IPat     -> pat
  IType    -> ty
  IKind    -> pure

program :: Simple Program -> Praxis (Simple Program)
program (a :< Program ds) = do
  ds <- decls ds
  return (a :< Program ds)

stmts :: [Simple Stmt] -> Praxis [Simple Stmt]
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

pack :: Source -> (Record b -> b) -> (a -> Praxis b) -> Record a -> Praxis b
pack s build f r = do
  r' <- traverse f r
  case Record.toList r' of
    []  -> throwAt s $ plain "illegal empty pack"
    [_] -> throwAt s $ plain "illegal single-field pack"
    _   -> return $ build r'

record :: Source -> (Record b -> b) -> (a -> Praxis b) -> Record a -> Praxis b
record s build f r = do
  r' <- traverse f r
  case Record.toList r' of
    [(Nothing, x)] -> return $ x
    [(Just _, _)]  -> throwAt s $ plain "illegal single-field record"
    _              -> return $ build r'

exp :: Simple Exp -> Praxis (Simple Exp)
exp (a :< x) = case x of

  Apply x (a' :< VarBang s) ->
    exp (a :< Apply x (a' :< Var s))

  Do ss       -> do
    ss' <- stmts ss
    return (a :< Do ss')

  Mixfix ts   -> mixfix ts

  Record r    -> record (fst a) (\r' -> a :< Record r') exp r

  VarBang s   -> throwAt (fst a) $ "observed variable " <> quote (plain s) <> " is not the argument of a function"

  _           -> (a :<) <$> recurse desugar x


decls :: [Simple Decl] -> Praxis [Simple Decl]
decls []            = pure []
decls (a :< d : ds) = case d of

  DeclSig n t -> do
    decls ds >>= \case
      (a' :< DeclVar m Nothing e) : ds | m == n -> return $ ((a <> a') :< DeclVar n (Just t) e) : ds
      _                                         -> throwAt (fst a) $ "declaration of " <> quote (plain n) <> " lacks an accompanying binding"

  DeclFun n ps e -> do
    ps <- mapM pat ps
    e  <- exp e
    let d = a :< DeclVar n Nothing (lambda ps e)
        lambda :: [Simple Pat] -> Simple Exp -> Simple Exp
        lambda     [] e = e
        lambda (p:ps) e = a :< Lambda p (lambda ps e)
    decls ds >>= \case
      []                                       -> return $ [d]
      (a' :< DeclVar m t as) : ds' | m == n    -> error "TODO multiple definitions"
      ds                                       -> return $ d:ds

  DeclData n t as -> do
    t' <- traverse tyPat t
    as' <- traverse dataAlt as
    ds' <- decls ds
    return (a :< DeclData n t' as' : ds')


dataAlt :: Simple DataAlt -> Praxis (Simple DataAlt)
dataAlt (a :< x) = (a :<) <$> case x of

  DataAlt n ts ->  DataAlt n <$> traverse ty ts


-- TODO check for overlapping patterns?
pat :: Simple Pat -> Praxis (Simple Pat)
pat (a :< x) = case x of

  PatRecord r -> record (fst a) (\r' -> a :< PatRecord r') pat r

  _           -> (a :<) <$> recurse desugar x


ty :: Simple Type -> Praxis (Simple Type)
ty (a :< x) = case x of

  TyRecord r -> record (fst a) (\r' -> a :< TyRecord r') ty r

  TyPack r   -> pack (fst a) (\r' -> a :< TyPack r') ty r

  _          -> (a :<) <$> recurse desugar x


tyPat :: Simple TyPat -> Praxis (Simple TyPat)
tyPat (a :< x) = case x of

  TyPatPack r -> pack (fst a) (\r' -> a :< TyPatPack r') tyPat r

  _           -> (a :<) <$> recurse desugar x


type MTok = DAG.Tok (Tag (Source, ()) Op) (Simple Exp)

tok :: Simple Tok -> Praxis MTok
tok (a :< TOp op) = pure (DAG.TOp (a :< op))
tok (a :< TExp e) = DAG.TExpr <$> exp e

mixfix :: [Simple Tok] -> Praxis (Simple Exp)
mixfix ts = do
  ts' <- mapM tok ts
  -- TODO do something with report?
  let (parses, _) = fullParses (parser (DAG.simpleMixfixExpression opTable)) ts'
  case parses of [e] -> return e
                 _   -> error "TODO resolve error make a proper error for this (ambiguous mixfix parse)"

type OpTable = DAG.DAG Int [DAG.Op (Tag (Source, ()) Op) (Simple Exp)]

raw :: a -> Tag (Source, ()) a
raw x = (Phantom, ()) :< x

-- TODO build this dynamically from bindings
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
  where build a s n = DAG.Op { DAG.fixity = DAG.Infix a, DAG.parts = [raw $ QString { qualification = [], name = s }], DAG.build = \[e1, e2] -> build' n e1 e2 }
        build' n e1 e2 = raw $ Apply (raw $ Var n) (raw $ Record (pair e1 e2)) :: Simple Exp -- TODO annotations?
        add = build DAG.LeftAssoc "+" "add"
        sub = build DAG.LeftAssoc "-" "sub"
        mul = build DAG.LeftAssoc "*" "mul"
        dot = build DAG.RightAssoc "." "dot"

