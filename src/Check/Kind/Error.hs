module Check.Kind.Error
  ( Error(..)
  ) where

import           Check.Kind.Annotate
import           Check.Kind.Constraint
import           Common

data Error = Contradiction (Kinded KindConstraint)
           | Stuck
