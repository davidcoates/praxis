module Check.Error
  ( TypeError(..)
  ) where

import Check.Derivation
import Pos
import AST (Name)

data TypeError = Contradiction Derivation
               | Underdefined Derivation
               | NotInScope String

instance Show TypeError where
  show (Contradiction d) = show d
  show (Underdefined d)  = "Failed to completely deduce the unification variable(s) present in: " ++ show d
  show (NotInScope s) = "Not in scope: " ++ s

