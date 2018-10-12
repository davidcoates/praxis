module Check.Type.Check
  ( Checkable(..)
  ) where

import           AST                 (Program)
import           Check.Type.Annotate
import           Parse.Annotate
import           Praxis
import           Type                (Type)

class Checkable a where
  check :: Parsed a -> Praxis (Typed a)

instance Checkable Program where
  check = undefined

instance Checkable Type where
  check = undefined
