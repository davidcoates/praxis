{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE OverloadedStrings      #-}

module Parse.Desugar
  ( run
  ) where

import           Annotate
import           AST
import           Common
import           Introspect
import           Kind
import           Praxis
import           Record                 (Record, pair)
import qualified Record                 (toList)
import           Type

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

run :: Recursive a => Parsed a -> Praxis (Parsed a)
run x = save stage $ do
  stage .= Desugar
  x' <- desugar x
  output x'
  return x'

desugar :: Recursive a => Parsed a -> Praxis (Parsed a)
desugar x = ($ x) $ case typeof x of
  IProgram -> program
  IExp     -> exp
  IPat     -> pat
  IType    -> ty
  IKind    -> pure

program :: Parsed Program -> Praxis (Parsed Program)
program (a :< Program ds) = do
  ds <- decls ds
  return (a :< Program ds)

stmts :: [Parsed Stmt] -> Praxis [Parsed Stmt]
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
    [(Just _, _)]  -> throwAt s $ plain "illegal single-field record"
    _              -> return $ build r'

exp :: Parsed Exp -> Praxis (Parsed Exp)
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


decls :: [Parsed Decl] -> Praxis [Parsed Decl]
decls []              = pure []
decls (a :< d : ds) = case d of

  DeclSig n t -> do
    ds <- decls ds
    case ds of (a' :< DeclVar m Nothing e) : ds | m == n -> return $ ((a <> a') :< DeclVar n (Just t) e) : ds
               _                                         -> throwAt (fst a) $ "declaration of " <> quote (plain n) <> " lacks an accompanying binding"

  DeclFun n ps e -> do
    ps <- mapM pat ps
    e  <- exp e
    let d = a :< DeclVar n Nothing (lambda ps e)
        lambda :: [Parsed Pat] -> Parsed Exp -> Parsed Exp
        lambda     [] e = e
        lambda (p:ps) e = a :< Lambda p (lambda ps e)
    ds <- decls ds
    case ds of []                                       -> return $ [d]
               (a' :< DeclVar m t as) : ds' | m == n    -> error "TODO multiple definitions"
                                            | otherwise -> return $ d:ds

-- TODO check for overlapping patterns?
pat :: Parsed Pat -> Praxis (Parsed Pat)
pat (a :< x) = case x of

  PatRecord r -> record (fst a) (\r' -> a :< PatRecord r') pat r

  _           -> (a :<) <$> recurse desugar x


ty :: Parsed Type -> Praxis (Parsed Type)
ty (a :< x) = case x of

  TyRecord r -> record (fst a) (\r' -> a :< TyRecord r') ty r

  _          -> (a :<) <$> recurse desugar x


type MTok = DAG.Tok (Tag (Source, ()) Op) (Parsed Exp)

tok :: Parsed Tok -> Praxis MTok
tok (a :< TOp op) = pure (DAG.TOp (a :< op))
tok (a :< TExp e) = DAG.TExpr <$> exp e

mixfix :: [Parsed Tok] -> Praxis (Parsed Exp)
mixfix ts = do
  ts' <- mapM tok ts
  -- TODO do something with report?
  let (parses, _) = fullParses (parser (DAG.simpleMixfixExpression opTable)) ts'
  case parses of [e] -> return e
                 _   -> error "TODO resolve error make a proper error for this (ambiguous mixfix parse)"

type OpTable = DAG.DAG Int [DAG.Op (Tag (Source, ()) Op) (Parsed Exp)]

raw :: a -> Tag (Source, ()) a
raw x = (Phantom, ()) :< x

-- TODO build this dynamically from bindings
opTable :: OpTable
opTable = DAG.DAG
  { DAG.nodes = [6, 7, 9]
  , DAG.neighbors = \x -> case x of
      6 -> [7,9]
      7 -> [9]
      9 -> []
  , DAG.value = \x -> case x of
      6 -> [ add, sub ]
      7 -> [ mul ]
      9 -> [ dot ]
  }
  where build a s n = DAG.Op { DAG.fixity = DAG.Infix a, DAG.parts = [raw $ QString { qualification = [], name = s }], DAG.build = \[e1, e2] -> build' n e1 e2 }
        build' n e1 e2 = raw $ Apply (raw $ Var n) (raw $ Record (pair e1 e2)) :: Parsed Exp -- TODO annotations?
        add = build DAG.LeftAssoc "+" "add"
        sub = build DAG.LeftAssoc "-" "sub"
        mul = build DAG.LeftAssoc "*" "mul"
        dot = build DAG.RightAssoc "." "dot"

