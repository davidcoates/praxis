module Checker.Error
  ( TypeErrorTy(..)
  , TypeError(..)
  ) where

import AST (Error)
import Checker.Constraint (Constraint)

data TypeErrorTy = Contradiction Constraint
                 | NotInScope String
                 deriving (Show)

type TypeError = Error TypeErrorTy
