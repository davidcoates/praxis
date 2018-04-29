module Parse.Desugar
  ( desugar
  , module Parse.Desugar.AST
  ) where

import Parse.Parse.AST (Op, Tok(..))
import qualified Parse.Parse.AST as Parse
import Parse.Desugar.AST
import Parse.Desugar.Infix
import Tag
import Compiler
import Error

import Control.Monad (unless)
import Control.Applicative (liftA2, liftA3)
import Control.Arrow (left)
import Data.Map (Map)
import qualified Data.Map as Map
import Source

opTable :: Map Op Fixity
opTable = undefined -- Map.fromList [("+", Fixity (6, Leftfix)), ("==", Fixity (4, Nonfix))]

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
  Parse.Infix ts    -> resolve opTable ts
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
            build (Right (a :< FunDecl n d) : ds) e = a :< Let n d (build ds e)

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
    case ds of (Right (a :< FunDecl m e)) : ds | m == n -> return $ Right (a :< FunDecl n (a :< Signature e t)) : ds
               _                                        -> throwDeclError (LacksBinding n a)
  Parse.FunDecl n ps e -> do
    let i = length ps

    let hasName :: Name -> (Parse.Annotated Parse.Decl -> Bool)
        hasName n (_ :< Parse.FunDecl m _ _) | n == m = True
        hasName _ _ = False
    
    let (as, bs) = span (hasName n) ds
    
    if any (hasName n) bs then error "make a proper error message here about multiple definitions" else pure ()

    -- Check arity
    sequence . (flip map) as $ \(a' :< Parse.FunDecl _ ps _) -> let j = length ps in
      if i /= j then throwDeclError (MismatchedArity n (a, i) (a', j)) else pure ()

    ds <- desugarDecls ds

    if i == 0
    then
      if length as == 0
      then do
        e <- desugarExp e
        let d = Right (a :< FunDecl n e)
        return (d : ds)
      else
        error "blah multiple definitions for nullary" -- TODO make this a propery error
    else
      if i == 1
      then do
        alts <- sequence . (flip map) as $ \(_ :< Parse.FunDecl _ [p] e) -> liftA2 (,) (desugarPat p) (desugarExp e)
        v <- freshVar
        let d = Right (a :< FunDecl n (a :< Lambda v (a :< Case (a :< Var v) alts))) -- TODO phony pos?
        return (d : ds)
      else
        error "only unary or nullary functions currently supported"

desugarPat :: Parse.Annotated Parse.Pat -> Compiler (Annotated Pat)
desugarPat = undefined

-- TODO
-- REPLACE WITH MY MIXFIX PARSER
resolve :: Map Op Fixity -> [Annotated Tok] -> Compiler (Exp (Tag Source))
resolve fixityTable ts = undefined
