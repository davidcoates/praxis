{-# LANGUAGE TemplateHaskell #-}

module Check.State
  ( State(..)
  , requirements
  , assumptions
  , counts
  , scopes

  , emptyState
  ) where

import           Common
import           Term

import           Control.Lens    (makeLenses)
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import           Data.Set        (Set)
import qualified Data.Set        as Set


data State c = State
  { _requirements :: Set (Annotated (Requirement c))
  , _assumptions  :: Set c
  , _counts       :: Map Name Int
  , _scopes       :: Map Name Int
  }

makeLenses ''State

emptyState :: State c
emptyState = State
  { _requirements   = Set.empty
  , _assumptions    = Set.empty
  , _counts         = Map.empty
  , _scopes         = Map.empty
  }
