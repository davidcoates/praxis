{-# LANGUAGE TemplateHaskell #-}

module Core.State
  ( State
  , capturesByName
  , liftedFunctions

  , emptyState
  ) where

import           Common
import           Term

import           Control.Lens    (makeLenses)
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map


data State = State
  { _capturesByName  :: Map Name Captures
  , _liftedFunctions :: [Annotated DeclTerm]
  }

emptyState :: State
emptyState = State
  { _capturesByName = Map.empty
  , _liftedFunctions = []
  }

makeLenses ''State
