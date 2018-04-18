module Parse.Desugar.Desugar
  ( desugar
  , module Parse.Desugar.AST
  , module Parse.Desugar.Error
  ) where

import Parse.Parse (Op, Tok(..))
import qualified Parse.Parse as Parse
import Parse.Desugar.AST
import Parse.Desugar.Error
import Parse.Desugar.Infix
import Control.Monad (unless)
import Control.Applicative (liftA2, liftA3)

import Compile
import Data.Map (Map)
import qualified Data.Map as Map

opTable :: Map Op Fixity
opTable = Map.fromList [("+", Fixity (6, Leftfix)), ("==", Fixity (4, Nonfix))]

desugar :: Compiler String ()
desugar = do
  set stage Desugar
  e  <- get sugaredAST
  e' <- desugarExp e
  set desugaredAST e'

desugarExp :: Parse.AST -> Compiler DesugarError (Annotated Exp)
desugarExp (Parse.Infix _ ts) = resolve opTable ts
desugarExp (Parse.Lit a lit)     = pure (Lit a lit)
desugarExp (Parse.Var a s)       = pure (Var a s)
desugarExp (Parse.If a e1 e2 e3) = liftA3 (If a) (desugarExp e1) (desugarExp e2) (desugarExp e3)
desugarExp (Parse.Apply a x y)   = liftA2 (Apply a) (desugarExp x) (desugarExp y) 

-- TODO
-- REPLACE WITH MY MIXFIX PARSER
resolve :: Map Op Fixity -> [Annotated Tok] -> Compiler DesugarError (Annotated Exp)
resolve fixityTable ts = undefined
