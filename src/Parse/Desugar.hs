{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}

module Parse.Desugar
  ( Desugarable(..)
  ) where

import           AST
import           Common
import           Error
import           Introspect             (Recursive)
import           Parse.Annotate
import           Praxis
import           Record                 (pair)
import           Type                   (Kind, Type)

import           Control.Applicative    (Const, liftA2, liftA3)
import           Control.Arrow          (left)
import           Control.Monad          (unless)
import           Data.List              (intersperse)
import           Data.Map               (Map)
import qualified Data.Map               as Map
import           Data.Monoid            ((<>))
import           Prelude                hiding (exp, log)
import           Text.Earley
import qualified Text.Earley.Mixfix.DAG as DAG

class Desugarable a where
  desugar :: (Parsed a) -> Praxis (Parsed a)

desugar' :: (Recursive a) => ((Parsed a) -> Praxis (Parsed a)) -> (Parsed a) -> Praxis (Parsed a)
desugar' f x = save stage $ do
  stage .= Desugar
  x' <- f x
  log Debug x'
  return x'

instance Desugarable Program where
  desugar = desugar' program

instance Desugarable Exp where
  desugar = desugar' exp

instance Desugarable Type where
  desugar = pure

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

exp :: Parsed Exp -> Praxis (Parsed Exp)
exp (a :< x) = case x of

  Apply x (a' :< VarBang s) ->
    exp (a :< Apply x (a' :< Var s))

  Apply x y   -> do
    x' <- exp x
    y' <- exp y
    return (a :< Apply x' y')

  -- exp (a :< Apply (a :< Cases alts) e)
  Case e alts  -> do
    e' <- exp e
    alts' <- sequence $ map alt alts
    return (a :< Case e' alts')
      where alt (p, e) = liftA2 (,) (pat p) (exp e)

  Cases alts -> do
    alts' <- sequence $ map alt alts
    return (a :< Cases alts')
      where alt (p, e) = liftA2 (,) (pat p) (exp e)

  Do ss       -> do
    ss' <- stmts ss
    return (a :< Do ss')

  If e1 e2 e3 -> do
    e1' <- exp e1
    e2' <- exp e2
    e3' <- exp e3
    return (a :< If e1' e2' e3')

  Mixfix ts   -> mixfix ts

  Lit lit     -> pure (a :< Lit lit)

  Read n e    -> do
    e' <- exp e
    return (a :< Read n e')

  Record r    -> do
    r' <- traverse exp r
    return (a :< Record r')

  Sig e t     -> do
    e' <- exp e
    return (a :< Sig e' t)

  Var s       -> pure (a :< Var s)

  VarBang s   -> throwSyntaxError (BangError (fst a) s)


throwSyntaxError :: SyntaxError -> Praxis a
throwSyntaxError = throwError . SyntaxError

decls :: [Parsed Decl] -> Praxis [Parsed Decl]
decls []              = pure []
decls (a :< d : ds) = case d of

  DeclSig n t -> do
    ds <- decls ds
    case ds of (a' :< DeclVar m Nothing e) : ds | m == n -> return $ ((a <> a') :< DeclVar n (Just t) e) : ds
               _                                       -> throwSyntaxError (LacksBinding n (fst a))

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

  PatRecord r -> do
    r' <- traverse pat r
    return (a :< PatRecord r)

  PatVar x    -> pure (a :< PatVar x)

  PatLit l    -> pure (a :< PatLit l)


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

