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

check :: Term a => Annotated a -> Praxis (Annotated a)
check term = do
  system .= initialSystem
  Kind.check term >>= Type.check
