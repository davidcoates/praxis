{-# LANGUAGE TypeFamilies #-}

module Parse.Annotate
  ( Parsed
  ) where

import           Common
import           Introspect
import           Stage      (Parse)

type instance Annotation Parse a = ()

type Parsed a = Annotated Parse a

instance Complete Parse where
  complete _ _ _ = pure ()
