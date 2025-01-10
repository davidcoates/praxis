{-# LANGUAGE TemplateHaskell #-}

module Parse.State
  ( State(..)
  , opContext
  , typeSynonyms
  , emptyState

  , Fixity(..)
  , OpDefns
  , OpContext(..)
  , defns
  , levels
  , prec

  ) where

import           Common
import           Term

import           Control.Lens    (makeLenses)
import           Data.Array      (array)
import           Data.Graph      (Graph)
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map


data Fixity
  = Infix (Maybe Assoc)
  | Prefix
  | Postfix
  | Closed
  deriving (Eq, Ord)

type OpDefns = Map Op (Name, Fixity)

data OpContext = OpContext { _defns :: OpDefns, _levels :: [[Op]], _prec :: Graph }

makeLenses ''OpContext

data State = State
  { _opContext    :: OpContext
  , _typeSynonyms :: Map Name (Annotated Type)
  }

makeLenses ''State

emptyState :: State
emptyState = State
  { _opContext    = OpContext { _defns = Map.empty, _prec = array (0, -1) [], _levels = [] }
  , _typeSynonyms = Map.empty
  }
