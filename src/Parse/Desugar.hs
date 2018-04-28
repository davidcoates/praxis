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
opTable = Map.fromList [("+", Fixity (6, Leftfix)), ("==", Fixity (4, Nonfix))]

desugar :: Compiler ()
desugar = do
  set stage Desugar
  e  <- get sugaredAST
  e' <- desugarExp e
  set desugaredAST e'
  debugPrint e'

desugarExp :: Parse.Annotated Parse.Exp -> Compiler (Annotated Exp)
desugarExp = rec $ \a x -> fmap (a :<) $ case x of
  Parse.Infix ts    -> resolve opTable ts
  Parse.Lit lit     -> pure (Lit lit)
  Parse.Var s       -> pure (Var s)
  Parse.If e1 e2 e3 -> liftA3 If (desugarExp e1) (desugarExp e2) (desugarExp e3)
  Parse.Apply x y   -> liftA2 Apply (desugarExp x) (desugarExp y)
  Parse.Let (_ :< Parse.FunDecl n e1) e2 -> liftA2 (\e1 e2 -> Let n e1 e2) (desugarExp e1) (desugarExp e2)  -- TODO fixity decls

-- TODO
-- REPLACE WITH MY MIXFIX PARSER
resolve :: Map Op Fixity -> [Annotated Tok] -> Compiler (Exp (Tag Source))
resolve fixityTable ts = undefined
