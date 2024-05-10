module Check.Type.Concrete
  ( canTriviallyClone
  , canTriviallyDispose
  ) where

import           Common
import           Praxis
import           Term

canTriviallyClone :: Annotated Type -> Praxis Bool
canTriviallyClone t = error "canTriviallyClone"

canTriviallyDispose :: Annotated Type -> Praxis Bool
canTriviallyDispose t = error "canTriviallyDispose"
