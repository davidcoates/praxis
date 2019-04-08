module Check.Kind.Error
  ( Error(..)
  ) where

import           Check.Kind.Annotate
import           Check.Kind.Constraint
import           Common

data Error = Contradiction (Kinded KindConstraint)
           | Stuck

instance Show Error where
  show e = case e of
    Contradiction c -> "Contradiction: " ++ show c
    Stuck           -> "Infinite loop detected :("
