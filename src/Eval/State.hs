{-# LANGUAGE TemplateHaskell #-}

module Eval.State
  ( State(..)
  , valueEnv
  , emptyState

  , ValueEnv(..)
  ) where

import           Common
import           Eval.Value
import           Term

import           Control.Lens    (makeLenses)
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map


type ValueEnv = Map Name Value

data State = State
  { _valueEnv :: ValueEnv -- Value environment
  }

makeLenses ''State

emptyState :: State
emptyState = State
  { _valueEnv = Map.empty
  }
