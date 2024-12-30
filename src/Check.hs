module Check
  ( run
  ) where

import qualified Check.Kind.Check as Kind
import qualified Check.Type.Check as Type
import           Common
import           Introspect
import           Praxis
import           Term

run :: Term a => Annotated a -> Praxis (Annotated a)
run term = do
  Kind.run term >>= Type.run
