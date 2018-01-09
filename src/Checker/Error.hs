module Checker.Error
  ( TypeErrorTy(..)
  , TypeError(..)
  ) where

import AST (Error)
import Checker.Constraint (Constraint)

data TypeErrorTy = Contradiction Constraint

type TypeError = Error TypeErrorTy
