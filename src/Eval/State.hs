{-# LANGUAGE TemplateHaskell #-}

module Eval.State
  ( State(..)
  , vEnv
  , fEnv
  , emptyState

  , VEnv(..)
  ) where

import           Common
import           Eval.Value
import           Term

import           Control.Lens (makeLenses)
import qualified Env.Strict


type VEnv = Env.Strict.Env Value

data State = State
  { _vEnv :: VEnv -- Value environment (globals)
  , _fEnv :: VEnv -- Frame environment (locals)
  }

makeLenses ''State

emptyState :: State
emptyState = State
  { _vEnv = Env.Strict.empty
  , _fEnv = Env.Strict.empty
  }
