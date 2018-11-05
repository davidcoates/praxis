module Check.Type.Error
  ( Error(..)
  ) where

import           Check.Type.Annotate
import           Check.Type.Constraint
import           Common

data Error = Contradiction (Typed TypeConstraint)
           | Stuck
           | Underdefined (Typed TypeConstraint)

