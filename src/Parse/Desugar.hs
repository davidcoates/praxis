module Parse.Desugar
  ( desugar
  , module Parse.Desugar.AST
  ) where

import Common
import Compiler
import Error
import Parse.Desugar.AST
import Parse.Parse.AST (Op)
import qualified Parse.Parse.AST as Parse
import Record (pair)
import Source
import Tag

import Control.Applicative (liftA2, liftA3)
import Control.Arrow (left)
import Control.Monad (unless)
import Data.List (intersperse)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Monoid ((<>))
import Prelude hiding (exp)
import Text.Earley
import qualified Text.Earley.Mixfix.DAG as DAG


desugar :: Compiler ()
desugar = setIn stage Desugar $ do
  p  <- get sugaredAST
  p' <- program p
  set desugaredAST p'
  debugPrint p'

program :: Parse.Annotated Parse.Program -> Compiler (Annotated Program)
program (a :< Parse.Program ds) = do
  ds <- decls ds
  return (a :< Program ds)

exp :: Parse.Annotated Parse.Exp -> Compiler (Annotated Exp)
exp = rec $ \a x -> fmap (a :<) $ case x of
  Parse.Apply x y   -> liftA2 Apply (exp x) (exp y)
  Parse.Case _ _    -> error "TODO case"
  Parse.Do _        -> error "TODO do"
  Parse.If e1 e2 e3 -> liftA3 If (exp e1) (exp e2) (exp e3)
  Parse.Mixfix ts    -> (\(_ :< e) -> e) <$> mixfix ts
  Parse.Lit lit     -> pure (Lit lit)
  Parse.Read n e    -> Read n <$> exp e
  Parse.Record r    -> Record <$> traverse exp r
  Parse.Sig e t     -> (\e -> Sig e t) <$> exp e
  Parse.Var s       -> pure (Var s)
  Parse.VarBang s   -> error "TODO varbang"


throwDeclError :: DeclError -> Compiler a
throwDeclError = throwError . SyntaxError . DeclError

decls :: [Parse.Annotated Parse.Decl] -> Compiler [Annotated Decl]
decls []              = pure []
decls ((a :< d) : ds) = case d of

  Parse.DeclSig n t -> do
    ds <- decls ds
    case ds of (a' :< DeclFun m Nothing i as) : ds | m == n -> return $ ((a <> a') :< DeclFun n (Just t) i as) : ds
               _                                            -> throwDeclError (LacksBinding n a)
  
  Parse.DeclFun n ps e -> do    
    ps <- mapM pat ps
    e  <- exp e

    ds <- decls ds
    case ds of (a' :< DeclFun m t i as) : ds' | m /= n         -> return $ (a :< DeclFun n Nothing (length ps) [(ps, e)]) : ds
                                              | i /= length ps -> throwDeclError (MismatchedArity n (a, length ps) (a', i))
                                              | null ps        -> error "TODO multiple definitions for nullary"
                                              | otherwise      -> return $ ((a <> a') :< DeclFun m t i ((ps, e) : as)) : ds'
               []                                              -> return $ [a :< DeclFun n Nothing (length ps) [(ps, e)]]


pat :: Parse.Annotated Parse.Pat -> Compiler (Annotated Pat)
pat = rec $ \a x -> fmap (a :<) $ case x of
  Parse.PatRecord r -> PatRecord <$> sequence (fmap pat r)
  Parse.PatVar    x -> pure (PatVar x) 
  Parse.PatLit    l -> pure (PatLit l)

type Tok = DAG.Tok (Tag Source Op) (Annotated Exp)

tok :: Parse.Annotated Parse.Tok -> Compiler Tok
tok (a :< Parse.TOp op) = pure (DAG.TOp (a :< op))
tok (a :< Parse.TExp e) = DAG.TExpr <$> exp e

mixfix :: [Parse.Annotated Parse.Tok] -> Compiler (Annotated Exp)
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
