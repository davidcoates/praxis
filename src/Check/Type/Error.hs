module Check.Type.Error
  ( Error(..)
  ) where

import           Check.Type.Annotate
import           Check.Type.Constraint
import           Common

data Error = Contradiction (Typed TypeConstraint)
           | Stuck
           | Underdefined (Typed TypeConstraint)

instance Show Error where
  show e = case e of
    Contradiction c -> "Contradiction: " ++ show c
    Stuck           -> "Infinite loop detected :("
    Underdefined c  -> "Failed to completely deduce the unification variable(s) present in: " ++ show c
