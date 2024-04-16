module Check
  ( check
  ) where

import qualified Check.Kind.Check as Kind
import qualified Check.Type.Check as Type
import           Common
import           Introspect
import           Praxis
import           Term

check :: Term a => Annotated a -> Praxis (Annotated a)
check term = do
  Kind.check term >>= Type.check
