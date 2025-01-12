{-# LANGUAGE DataKinds       #-}
{-# LANGUAGE TemplateHaskell #-}

module Parse.State
  ( State(..)
  , opState
  , typeSynonyms
  , emptyState

  , Fixity(..)
  , OpDefinitions
  , OpNodes
  , OpState(..)
  , definitions
  , nodes
  , precedence

  ) where

import           Common
import           Stage
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

type OpDefinitions = Map (Annotated Parse Op) (Name, Fixity)

type OpNodes = [[Annotated Parse Op]]

data OpState = OpState
  { _definitions :: OpDefinitions
  , _nodes       :: OpNodes
  , _precedence  :: Graph
  }

makeLenses ''OpState

emptyOpState :: OpState
emptyOpState = OpState
  { _definitions = Map.empty
  , _nodes = []
  , _precedence = array (0, -1) []
  }

data State = State
  { _opState      :: OpState
  , _typeSynonyms :: Map Name (Annotated Parse Type)
  }

makeLenses ''State

emptyState :: State
emptyState = State
  { _opState      = emptyOpState
  , _typeSynonyms = Map.empty
  }
