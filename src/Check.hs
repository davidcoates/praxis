module Check
  ( check
  ) where

import           Check.Annotate
import qualified Check.Kind.Check as Kind
import qualified Check.Type.Check as Type
import           Introspect
import           Parse.Annotate
import           Praxis

check :: Recursive a => Parsed a -> Praxis (Kinded a)
check x = Type.check x >>= Kind.check
