{-# LANGUAGE TemplateHaskell #-}

module Monomorphize.State
  ( State(..)
  , instances
  , exportedDecls
  , sourceDecls
  , emptyState
  ) where

import           Common
import           Stage
import           Term

import           Control.Lens    (makeLenses)
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map


data State = State
  { _instances     :: Map (Name, [Annotated TypeCheck Type]) Name
  -- ^ Maps (original polymorphic name, concrete type args) to the generated monomorphic name.
  -- Structured representation; name mangling is deferred to downstream stages.
  , _exportedDecls :: [Annotated Monomorphize Decl]
  -- ^ Accumulated output declarations (in emission order).
  , _sourceDecls   :: Map Name (Annotated TypeCheck DeclTerm)
  -- ^ Source definitions of polymorphic functions, for on-demand specialization.
  }

makeLenses ''State

emptyState :: State
emptyState = State
  { _instances     = Map.empty
  , _exportedDecls = []
  , _sourceDecls   = Map.empty
  }
