{-# LANGUAGE TemplateHaskell #-}

module Monomorphize.State
  ( State(..)
  , instances
  , exportedDecls
  , sourceDecls
  , sourceDataDecls
  , conToDataType
  , emptyState
  ) where

import           Common
import           Stage
import           Term

import           Control.Lens    (makeLenses)
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map


data State = State
  { _instances       :: Map (Name, [Annotated TypeCheck Type]) Name
  -- ^ Maps (original polymorphic name, concrete type args) to the generated monomorphic name.
  -- Structured representation; name mangling is deferred to downstream stages.
  , _exportedDecls   :: [Annotated Monomorphize Decl]
  -- ^ Accumulated output declarations (in emission order).
  , _sourceDecls     :: Map Name (Annotated TypeCheck DeclTerm)
  -- ^ Source definitions of polymorphic functions, for on-demand specialization.
  , _sourceDataDecls :: Map Name (Annotated TypeCheck DeclType)
  -- ^ Polymorphic DeclTypeData declarations keyed by data type name.
  , _conToDataType   :: Map Name Name
  -- ^ Maps each constructor name to its owning data type name.
  }

makeLenses ''State

emptyState :: State
emptyState = State
  { _instances       = Map.empty
  , _exportedDecls   = []
  , _sourceDecls     = Map.empty
  , _sourceDataDecls = Map.empty
  , _conToDataType   = Map.empty
  }
