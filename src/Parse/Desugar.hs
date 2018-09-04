{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}

module Parse.Desugar
  ( Desugarable(..)
  , module Parse.Desugar.AST
  ) where

import           Common
import           Error
import           Parse.Desugar.AST
import           Parse.Parse.AST        (Op)
import qualified Parse.Parse.AST        as Parse
import           Praxis
import           Record                 (pair)
import           Source
import           Tag
import           Type                   (Kind, Type)

import           Control.Applicative    (liftA2, liftA3)
import           Control.Arrow          (left)
import           Control.Monad          (unless)
import           Data.List              (intersperse)
import           Data.Map               (Map)
import qualified Data.Map               as Map
import           Data.Monoid            ((<>))
import           Prelude                hiding (exp, log)
import           Text.Earley
import qualified Text.Earley.Mixfix.DAG as DAG

type Annotated a = Tagged Source a

class Show b => Desugarable a b | a -> b where
  desugar' :: a -> Praxis b
  desugar  :: a -> Praxis b
  desugar x = save stage $ do
    set stage Desugar
    x' <- desugar' x
    log Debug x'
    return x'

instance Desugarable (Annotated Parse.Program) (Annotated Program) where
  desugar' = program

instance Desugarable (Annotated Parse.Exp) (Annotated Exp) where
  desugar' = exp

instance Desugarable (Annotated Type) (Annotated Type) where
  desugar' = pure

instance Desugarable Kind Kind where
  desugar' = pure

program :: Annotated Parse.Program -> Praxis (Annotated Program)
program (a :< Parse.Program ds) = do
  ds <- decls ds
  return (a :< Program ds)

stmts :: [Annotated Parse.Stmt] -> Praxis [Annotated Stmt]
stmts     [] = pure []
stmts (s:ss) | a :< Parse.StmtExp e <- s = do
                e' <- exp e
                ss' <- stmts ss
                return (a :< StmtExp e' : ss')
             | otherwise = do
                let (ds, rs) = span isStmtDecl (s:ss)
                ds' <- decls (map (\(_ :< Parse.StmtDecl d) -> d) ds)
                rs' <- stmts rs
                return $ map (\(a :< d) -> a :< StmtDecl (a :< d)) ds' ++ rs'
                  where isStmtDecl (_ :< Parse.StmtDecl _) = True
                        isStmtDecl _                       = False

exp :: Annotated Parse.Exp -> Praxis (Annotated Exp)
exp e = ($ e) $ rec $ \a x -> case x of

  Parse.Apply x (a' :< Parse.VarBang s) ->
    exp (a :< Parse.Apply x (a' :< Parse.Var s))

  Parse.Apply x y   -> do
    x' <- exp x
    y' <- exp y
    return (a :< Apply x' y')

  Parse.Case e alts  -> exp (a :< Parse.Apply (a :< Parse.Case e alts) e)

  Parse.Cases alts -> do
    alts' <- sequence $ map alt alts
    return (a :< Cases alts')
      where alt (p, e) = liftA2 (,) (pat p) (exp e)

  Parse.Do ss       -> do
    ss' <- stmts ss
    return (a :< Do ss')

  Parse.If e1 e2 e3 -> do
    e1' <- exp e1
    e2' <- exp e2
    e3' <- exp e3
    return (a :< If e1' e2' e3')

  Parse.Mixfix ts   -> mixfix ts

  Parse.Lit lit     -> pure (a :< Lit lit)

  Parse.Read n e    -> do
    e' <- exp e
    return (a :< Read n e')

  Parse.Record r    -> do
    r' <- traverse exp r
    return (a :< Record r')

  Parse.Sig e t     -> do
    e' <- exp e
    return (a :< Sig e' t)

  Parse.Var s       -> pure (a :< Var s)

  Parse.VarBang s   -> throwSyntaxError (BangError a s)


throwSyntaxError :: SyntaxError -> Praxis a
throwSyntaxError = throwError . SyntaxError

throwDeclError :: DeclError -> Praxis a
throwDeclError = throwSyntaxError . DeclError

decls :: [Annotated Parse.Decl] -> Praxis [Annotated Decl]
decls []              = pure []
decls (a :< d : ds) = case d of

  Parse.DeclSig n t -> do
    ds <- decls ds
    case ds of (a' :< DeclVar m Nothing e) : ds | m == n -> return $ ((a <> a') :< DeclVar n (Just t) e) : ds
               _                                         -> throwDeclError (LacksBinding n a)

  Parse.DeclFun n ps e -> do
    ps <- mapM pat ps
    e  <- exp e
    let d = a :< DeclVar n Nothing (lambda ps e)
        lambda     [] e = e
        lambda (p:ps) e = a :< Lambda p (lambda ps e)
    ds <- decls ds
    case ds of []                                       -> return $ [d]
               (a' :< DeclVar m t as) : ds' | m == n    -> error "TODO multiple definitions"
                                            | otherwise -> return $ d:ds

-- TODO check for overlapping patterns?
pat :: Annotated Parse.Pat -> Praxis (Annotated Pat)
pat p = ($ p) $ rec $ \a x -> case x of

  Parse.PatRecord r -> do
    r' <- traverse pat r
    return (a :< PatRecord r)

  Parse.PatVar x    -> pure (a :< PatVar x)

  Parse.PatLit l    -> pure (a :< PatLit l)


type Tok = DAG.Tok (Tag Source Op) (Annotated Exp)

tok :: Annotated Parse.Tok -> Praxis Tok
tok (a :< Parse.TOp op) = pure (DAG.TOp (a :< op))
tok (a :< Parse.TExp e) = DAG.TExpr <$> exp e

mixfix :: [Annotated Parse.Tok] -> Praxis (Annotated Exp)
mixfix ts = do
  ts' <- mapM tok ts
  -- TODO do something with report?
  let (parses, _) = fullParses (parser (DAG.simpleMixfixExpression opTable)) ts'
  case parses of [e] -> return e
                 _   -> error "TODO resolve error make a proper error for this (ambiguous mixfix parse)"

type OpTable = DAG.DAG Int [DAG.Op (Tag Source Op) (Annotated Exp)]

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
  where build a s n = DAG.Op { DAG.fixity = DAG.Infix a, DAG.parts = [Phantom :< QString { qualification = [], name = s }], DAG.build = \[e1, e2] -> build' n e1 e2 }
        build' n e1 e2 = Phantom :< Apply (Phantom :< Var n) (Phantom :< Record (pair e1 e2)) -- TODO annotations?
        add = build DAG.LeftAssoc "+" "add"
        sub = build DAG.LeftAssoc "-" "sub"
        mul = build DAG.LeftAssoc "*" "mul"
        dot = build DAG.RightAssoc "." "dot"

