{-# LANGUAGE DataKinds #-}

module Check
  ( run
  ) where

import qualified Check.Kind.Check as Kind
import qualified Check.Type.Check as Type
import           Common
import           Introspect
import           Praxis
import           Stage
import           Term


run :: IsTerm a => Annotated Parse a -> Praxis (Annotated TypeCheck a)
run term = Kind.run term >>= Type.run
