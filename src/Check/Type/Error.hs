module Check.Type.Error
  ( Error(..)
  ) where

import           Check.Type.Annotate
import           Check.Type.Constraint
import           Common
import           Tag

data Error = Contradiction (Typed (Const Constraint))
           | Stuck
           | Underdefined (Typed (Const Constraint))

