module Check.Error
  ( Error(..)
  ) where

import qualified Check.Kind.Error as Kind
import qualified Check.Type.Error as Type

import           Common
import           Source

data Error = NotInScope Name Source
           | TypeError Type.Error
           | KindError Kind.Error
