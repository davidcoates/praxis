-- Type checker

module Checker
  ( infer
  ) where

import AST hiding (Praxis)
import Type hiding (Constraint)
import Checker.Constraint
import Checker.Generator (generateExp)
import Checker.Solver (solve)
import Checker.TCMonad (runTC)
import Checker.Error

type Praxis a = Annotate (Type, SourcePos) a

infer :: Annotate SourcePos Exp -> Either TypeError (Praxis Exp)
infer e = runTC $ do
  (ast, cs) <- generateExp e
  subs <- solve cs
  let ft x = lookup x subs
  let fe x = Nothing
  return (mapExp (\(t,p) -> (subsType ft fe t,p)) ast)
