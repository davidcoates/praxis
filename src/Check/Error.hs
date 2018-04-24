module Check.Error
  ( Error(..)
  ) where

import Check.Derivation
import AST (Name)

data Error = Contradiction Derivation
           | Underdefined Derivation
           | NotInScope String

instance Show Error where
  show (Contradiction d) = show d
  show (Underdefined d)  = "Failed to completely deduce the unification variable(s) present in: " ++ show d
  show (NotInScope s)    = "Not in scope: " ++ s

