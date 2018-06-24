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
  ds <- desugarTopDecls ds
  return (a :< Program ds)

desugarExp :: Parse.Annotated Parse.Exp -> Compiler (Annotated Exp)
desugarExp = rec $ \a x -> fmap (a :<) $ case x of
  Parse.Infix ts    -> (\(_ :< e) -> e) <$> desugarInfix ts
  Parse.Unit        -> pure Unit
  Parse.Lit lit     -> pure (Lit lit)
  Parse.Var s       -> pure (Var s)
  Parse.If e1 e2 e3 -> liftA3 If (desugarExp e1) (desugarExp e2) (desugarExp e3)
  Parse.Apply x y   -> liftA2 Apply (desugarExp x) (desugarExp y)
  Parse.Let ds e    -> do
    ds <- desugarDecls ds
    e <- desugarExp e
    return (value (build ds e))
      where build :: [Either Name (Annotated Decl)] -> Annotated Exp -> Annotated Exp
            build [] e = e
            build (Left n : ds)  e = a :< LetBang n (build ds e)
            build (Right (a :< DeclFun n d) : ds) e = a :< Let n d (build ds e)

throwDeclError :: DeclError -> Compiler a
throwDeclError = throwError . SyntaxError . DeclError

desugarTopDecls :: [Parse.Annotated Parse.Decl] -> Compiler [Annotated Decl]
desugarTopDecls = fmap (map (\(Right d) -> d)) . desugarDecls -- See note at data Decl a in Parse/Parse/AST.hs

desugarDecls :: [Parse.Annotated Parse.Decl] -> Compiler [Either Name (Annotated Decl)]
desugarDecls [] = pure []
desugarDecls ((a :< d) : ds) = case d of

  Parse.Bang n -> fmap (Left n :) (desugarDecls ds)

  Parse.FunType n t -> do
    ds <- desugarDecls ds
    case ds of (Right (a :< DeclFun m e)) : ds | m == n -> return $ Right (a :< DeclFun n (a :< Signature e t)) : ds
               _                                        -> throwDeclError (LacksBinding n a)
  Parse.DeclFun n ps e -> do
    
    let i = length ps

    let hasName :: Name -> (Parse.Annotated Parse.Decl -> Bool)
        hasName n (_ :< Parse.DeclFun m _ _) | n == m = True
        hasName _ _ = False

    let (as, bs) = span (hasName n) ((a :< d): ds)

    if any (hasName n) bs then error "make a proper error message here about multiple definitions" else pure ()

    -- Check arity
    sequence . (flip map) as $ \(a' :< Parse.DeclFun _ ps _) -> let j = length ps in
      if i /= j then throwDeclError (MismatchedArity n (a, i) (a', j)) else pure ()

    ds <- desugarDecls bs

    if i == 0
    then
      if length as == 0
      then do
        e <- desugarExp e
        let d = Right (a :< DeclFun n e)
        return (d : ds)
      else
        error "blah multiple definitions for nullary" -- TODO make this a propery error
    else
      if i == 1
      then do
        alts <- sequence . (flip map) as $ \(_ :< Parse.DeclFun _ [p] e) -> liftA2 (,) (desugarPat p) (desugarExp e)
        v <- freshVar
        let d = Right (a :< DeclFun n (a :< Lambda v (a :< Case (a :< Var v) alts))) -- TODO phantom pos?
        return (d : ds)
      else
        error "only unary or nullary functions currently supported"

desugarPat :: Parse.Annotated Parse.Pat -> Compiler (Annotated Pat)
desugarPat = rec $ \a x -> fmap (a :<) $ case x of
  Parse.PatUnit  -> pure PatUnit
  Parse.PatVar x -> pure (PatVar x) 
  Parse.PatLit l -> pure (PatLit l)

type Tok = DAG.Tok (Tag Source Op) (Annotated Exp)

desugarTok :: Parse.Annotated Parse.Tok -> Compiler Tok
desugarTok (a :< Parse.TOp op) = pure (DAG.TOp (a :< op))
desugarTok (a :< Parse.TExp e) = DAG.TExpr <$> desugarExp e

desugarInfix :: [Parse.Annotated Parse.Tok] -> Compiler (Annotated Exp)
desugarInfix ts = do
  ts' <- sequence (map desugarTok ts)
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
{-
  where plus  = Op { fixity = Infix LeftAssoc, parts = QString { qualification = [], name = "+" }, build = \[(a :< e1),_,e2] -> }
        sub   = Op { fixity = Infix LeftAssoc, parts = QString { qualification = [], name = "-" }, build = \[e1,_,e2] }
        times = Op { fixity = Infix LeftAssoc, parts = QString { qualification = [], name = "*" }, build = \[e1,_,e2] }
              }undefined -- Map.fromList [("+", Fixity (6, Leftfix)), ("==", Fixity (4, Nonfix))]
-}
