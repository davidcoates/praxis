module Checker.Error
  ( TypeErrorTy(..)
  , TypeError(..)
  ) where

import AST (Error)
import Checker.Constraint (TConstraint)

data TypeErrorTy = Contradiction TConstraint
                 | NotInScope String

instance Show TypeErrorTy where
  show (Contradiction c) = show c
  show (NotInScope s) = "Not in scope: " ++ s

type TypeError = Error TypeErrorTy
