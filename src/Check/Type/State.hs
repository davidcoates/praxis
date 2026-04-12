{-# LANGUAGE TemplateHaskell #-}

module Check.Type.State
  ( TypeLocal
  , typeSolveLocal
  , emptyTypeLocal
  , TypeM
  ) where

import           Check.State         (Constraints, emptyConstraints)
import           Common              (makeLenses)
import           Control.Monad.State (StateT)
import           Praxis              (Praxis)
import           Stage


data TypeLocal = TypeLocal
  { _typeSolveLocal :: Constraints TypeCheck
  }

makeLenses ''TypeLocal

emptyTypeLocal :: TypeLocal
emptyTypeLocal = TypeLocal
  { _typeSolveLocal = emptyConstraints
  }

-- | The type-checking monad: local type state layered over Praxis.
type TypeM = StateT TypeLocal Praxis
