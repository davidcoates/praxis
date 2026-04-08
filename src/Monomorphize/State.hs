{-# LANGUAGE TemplateHaskell #-}

module Monomorphize.State
  ( State(..)
  , specializations
  , outputDecls
  , polyDecls
  , polyDataDecls
  , conToDataType
  , localPolyNames
  , localPendingDecls
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
  { _specializations   :: Map (Name, [Annotated TypeCheck Type]) Name
  -- ^ Maps (original polymorphic name, concrete type args) to the generated monomorphic name.
  -- Structured representation; name mangling is deferred to downstream stages.
  , _outputDecls       :: [Annotated Monomorphize Decl]
  -- ^ Accumulated output declarations (in emission order).
  , _polyDecls         :: Map Name (Annotated TypeCheck DeclTerm)
  -- ^ Source definitions of top-level polymorphic functions, for on-demand specialization.
  , _polyDataDecls     :: Map Name (Annotated TypeCheck DeclType)
  -- ^ Polymorphic DeclTypeData declarations keyed by data type name.
  , _conToDataType     :: Map Name Name
  -- ^ Maps each constructor name to its owning data type name.
  , _localPolyNames    :: Set Name
  -- ^ Names of Where-bound polymorphic functions currently in scope, for routing specializations.
  , _localPendingDecls :: [Annotated Monomorphize DeclTerm]
  -- ^ Monomorphic instances of local poly decls, awaiting insertion into the enclosing Where.
  }

makeLenses ''State

emptyState :: State
emptyState = State
  { _specializations   = Map.empty
  , _outputDecls       = []
  , _polyDecls         = Map.empty
  , _polyDataDecls     = Map.empty
  , _conToDataType     = Map.empty
  , _localPolyNames    = Set.empty
  , _localPendingDecls = []
  }
