{-# LANGUAGE TemplateHaskell #-}

module Check.System
  ( System
  , tySystem
  , kindSystem

  , initialSystem

  , module Type
  , module Kind
  ) where

import qualified Check.Kind.System as Kind
import qualified Check.Type.System as Type

import           Control.Lens      (makeLenses)

initialSystem :: System
initialSystem = System
  { _tySystem = Type.initialSystem
  , _kindSystem = Kind.initialSystem
  }

data System = System
  { _tySystem   :: Type.System
  , _kindSystem :: Kind.System
  }

makeLenses ''System

instance Show System where
  show _ = "<system>"
