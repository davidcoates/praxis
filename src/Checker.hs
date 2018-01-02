-- Type checker

module Checker
  ( test
  ) where

import AST hiding (Praxis)
import Type hiding (Constraint)
import Checker.Constraint
import Checker.Generator (generateExp)
import Checker.Solver (solve)
import Checker.TCMonad (runTC)
import Checker.Error

type Praxis a = Annotate (Type, SourcePos) a


-- infer :: Annotate SourcePos Exp -> Either TypeError (Praxis Exp)
-- infer = 

test :: Annotate SourcePos Exp -> Either TypeError (Annotate (Type, SourcePos) Exp, [Constraint], [(String,Pure)])
test a = runTC $ do
  (ast, cs) <- generateExp a
  subs <- solve cs
  return (ast, cs, subs)
