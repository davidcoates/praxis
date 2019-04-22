module Check.Type.Error
  ( Error(..)
  ) where

import           Annotate
import           Type

data Error = Contradiction (Typed Constraint)
           | Stuck
           | Underdefined (Typed Constraint)

instance Show Error where
  show e = case e of
    Contradiction c -> "Contradiction: " ++ show c
    Stuck           -> "Infinite loop detected :("
    Underdefined c  -> "Failed to completely deduce the unification variable(s) present in: " ++ show c
