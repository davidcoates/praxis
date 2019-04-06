module Check
  ( check
  ) where

import           Check.Annotate
import qualified Check.Kind.Check as Kind
import           Check.System
import qualified Check.Type.Check as Type
import           Common
import           Introspect
import           Parse.Annotate
import           Praxis

check :: Recursive a => Parsed a -> Praxis (Kinded a)
check x = do
  logStr Debug "test"
  system .= initialSystem
  logStr Debug "test"
  x' <- Type.check x
  logStr Debug "test"
  Kind.check x'
