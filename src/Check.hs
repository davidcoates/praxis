module Check
  ( check
  ) where

import qualified Check.Kind.Check as Kind
import           Check.System
import qualified Check.Type.Check as Type
import           Common
import           Introspect
import           Praxis
import           Term

check :: Recursive a => Parsed a -> Praxis (Kinded a)
check x = do
  system .= initialSystem
  x' <- Type.check x
  Kind.check x'
