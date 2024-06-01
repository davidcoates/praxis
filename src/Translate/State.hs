{-# LANGUAGE TemplateHaskell #-}

module Translate.State
  ( State
  , capturesByName
  , monoDeclsSeq
  , monoDeclsSet
  , polyDeclsByName

  , emptyState
  ) where

import           Common
import           Term

import           Control.Lens    (makeLenses)
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import           Data.Sequence   (Seq)
import qualified Data.Sequence   as Seq
import           Data.Set        (Set)
import qualified Data.Set        as Set


data State = State
  { _capturesByName  :: Map Name Captures
  , _monoDeclsSeq    :: Seq (Annotated Decl)
  , _monoDeclsSet    :: Set Name
  , _polyDeclsByName :: Map Name (Annotated Decl)
  }

emptyState :: State
emptyState = State
  { _capturesByName  = Map.empty
  , _monoDeclsSeq    = Seq.empty
  , _monoDeclsSet    = Set.empty
  , _polyDeclsByName = Map.empty
  }

makeLenses ''State
