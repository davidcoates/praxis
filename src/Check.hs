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

check :: Recursive a => Parsed a -> Praxis (Typed a)
check x = do
  system .= initialSystem
  Kind.check x >>= Type.check
