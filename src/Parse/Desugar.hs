module Parse.Desugar
  ( desugar
  , module Parse.Desugar.AST
  ) where

import Parse.Parse.AST (Op)
import qualified Parse.Parse.AST as Parse
import Parse.Desugar.AST
import Tag
import Compiler
import Error

import Control.Monad (unless)
import Data.Monoid ((<>))
import Control.Applicative (liftA2, liftA3)
import Control.Arrow (left)
import Data.Map (Map)
import qualified Data.Map as Map
import Source

import Record (pair)

import Text.Earley
import qualified Text.Earley.Mixfix.DAG as DAG
import Data.List (intersperse)

desugar :: Compiler ()
desugar = do
  set stage Desugar
  p  <- get sugaredAST
  p' <- desugarProgram p
  set desugaredAST p'
  debugPrint p'

desugarProgram :: Parse.Annotated Parse.Program -> Compiler (Annotated Program)
desugarProgram (a :< Parse.Program ds) = do
  ds <- desugarDecls ds
  return (a :< Program ds)

desugarExp :: Parse.Annotated Parse.Exp -> Compiler (Annotated Exp)
desugarExp = rec $ \a x -> fmap (a :<) $ case x of
  Parse.Apply x y   -> liftA2 Apply (desugarExp x) (desugarExp y)
  Parse.If e1 e2 e3 -> liftA3 If (desugarExp e1) (desugarExp e2) (desugarExp e3)
  Parse.Infix ts    -> (\(_ :< e) -> e) <$> desugarInfix ts
  Parse.Do ss       -> undefined -- TODO FIXME
  Parse.Lit lit     -> pure (Lit lit)
  Parse.Var s       -> pure (Var s)

throwDeclError :: DeclError -> Compiler a
throwDeclError = throwError . SyntaxError . DeclError

desugarDecls :: [Parse.Annotated Parse.Decl] -> Compiler [Annotated Decl]
desugarDecls []              = pure []
desugarDecls ((a :< d) : ds) = case d of

  Parse.DeclSig n t -> do
    ds <- desugarDecls ds
    case ds of (a' :< DeclFun m Nothing i as) : ds | m == n -> return $ ((a <> a') :< DeclFun n (Just t) i as) : ds
               _                                            -> throwDeclError (LacksBinding n a)
  
  Parse.DeclFun n ps e -> do    
    ps <- mapM desugarPat ps
    e  <- desugarExp e

    ds <- desugarDecls ds
    case ds of (a' :< DeclFun m t i as) : ds' | m /= n         -> return $ (a :< DeclFun n Nothing (length ps) [(ps, e)]) : ds
                                              | i /= length ps -> throwDeclError (MismatchedArity n (a, length ps) (a', i))
                                              | null ps        -> error "TODO multiple definitions for nullary"
                                              | otherwise      -> return $ ((a <> a') :< DeclFun m t i ((ps, e) : as)) : ds'
               []                                              -> return $ [a :< DeclFun n Nothing (length ps) [(ps, e)]]


desugarPat :: Parse.Annotated Parse.Pat -> Compiler (Annotated Pat)
desugarPat = rec $ \a x -> fmap (a :<) $ case x of
  Parse.PatRecord r -> PatRecord <$> sequence (fmap desugarPat r)
  Parse.PatVar    x -> pure (PatVar x) 
  Parse.PatLit    l -> pure (PatLit l)

type Tok = DAG.Tok (Tag Source Op) (Annotated Exp)

desugarTok :: Parse.Annotated Parse.Tok -> Compiler Tok
desugarTok (a :< Parse.TOp op) = pure (DAG.TOp (a :< op))
desugarTok (a :< Parse.TExp e) = DAG.TExpr <$> desugarExp e

desugarInfix :: [Parse.Annotated Parse.Tok] -> Compiler (Annotated Exp)
desugarInfix ts = do
  ts' <- mapM desugarTok ts
  -- TODO do something with report?
  let (parses, _) = fullParses (parser (DAG.simpleMixfixExpression opTable)) ts'
  case parses of [e] -> return e
                 _   -> error "TODO resolve error make a proper error for this (ambiguous infix parse)"

type OpTable = DAG.DAG Int [DAG.Op (Tag Source Op) (Annotated Exp)]

-- TODO build this dynamically from bindings
opTable :: OpTable
opTable = DAG.DAG
  { DAG.nodes = [6, 7]
  , DAG.neighbors = \x -> case x of
      6   -> [7]
      7   -> []
  , DAG.value = \x -> case x of
      6   -> [ add, sub ]
      7   -> [ mul ]
  }
  where build s n = DAG.Op { DAG.fixity = DAG.Infix DAG.LeftAssoc, DAG.parts = [Phantom :< QString { qualification = [], name = s }], DAG.build = \[e1, e2] -> build' n e1 e2 }
        build' n e1 e2 = Phantom :< Apply (Phantom :< Var n) (Phantom :< Record (pair e1 e2)) -- TODO annotations?
        add = build "+" "add"
        sub = build "-" "sub"
        mul = build "*" "mul"
