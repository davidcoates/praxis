module Check.Kind.Error
  ( Error(..)
  ) where

import           Annotate
import           Kind

data Error = Contradiction (Kinded Constraint)
           | Stuck

instance Show Error where
  show e = case e of
    Contradiction c -> "Contradiction: " ++ show c
    Stuck           -> "Infinite loop detected :("
