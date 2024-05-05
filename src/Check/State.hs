{-# LANGUAGE TemplateHaskell #-}

module Check.State
  ( State(..)
  , emptyState
  , requirements
  , assumptions
  ) where

import           Term

import           Control.Lens (makeLenses)
import           Data.Set     (Set)
import qualified Data.Set     as Set


data State c = State
  { _requirements :: [Annotated (Requirement c)] -- TODO colored string?
  , _assumptions  :: Set c
  }

emptyState :: State c
emptyState = State
  { _requirements = []
  , _assumptions  = Set.empty
  }

makeLenses ''State
