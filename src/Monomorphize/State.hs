{-# LANGUAGE DataKinds       #-}
{-# LANGUAGE TemplateHaskell #-}

module Monomorphize.State
  ( State(..)
  , specializations
  , exportedDecls
  , emptyState
  ) where

import           Common
import           Stage
import           Term

import           Control.Lens    (makeLenses)
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import           Data.Set        (Set)
import qualified Data.Set        as Set


data State = State
  { _specializations :: Map Name (Map Name [Annotated Monomorphize Decl])
  , _exportedDecls   :: [Annotated Monomorphize Decl]
  }

makeLenses ''State

emptyState :: State
emptyState = State
  { _specializations = Map.empty
  , _exportedDecls = []
  }
