module Check.Kind.Error
  ( Error(..)
  ) where

import           Check.Kind.Annotate
import           Check.Kind.Constraint
import           Common
import           Tag

data Error = Contradiction (Kinded (Const Constraint))
           | Stuck
