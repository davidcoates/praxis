{-# LANGUAGE TemplateHaskell #-}

module Monomorphize.State
  ( State(..)
  , instances
  , exportedDecls
  , sourceDecls
  , sourceDataDecls
  , conToDataType
  , localSourceDecls
  , localPendingDecls
  , emptyState
  ) where

import           Common
import           Stage
import           Term

import           Control.Lens    (makeLenses)
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map


data State = State
  { _instances         :: Map (Name, [Annotated TypeCheck Type]) Name
  -- ^ Maps (original polymorphic name, concrete type args) to the generated monomorphic name.
  -- Structured representation; name mangling is deferred to downstream stages.
  , _exportedDecls     :: [Annotated Monomorphize Decl]
  -- ^ Accumulated output declarations (in emission order).
  , _sourceDecls       :: Map Name (Annotated TypeCheck DeclTerm)
  -- ^ Source definitions of top-level polymorphic functions, for on-demand specialization.
  , _sourceDataDecls   :: Map Name (Annotated TypeCheck DeclType)
  -- ^ Polymorphic DeclTypeData declarations keyed by data type name.
  , _conToDataType     :: Map Name Name
  -- ^ Maps each constructor name to its owning data type name.
  , _localSourceDecls  :: Map Name (Annotated TypeCheck DeclTerm)
  -- ^ Source definitions of Where-bound polymorphic functions, scoped per Where expression.
  , _localPendingDecls :: [Annotated Monomorphize DeclTerm]
  -- ^ Specialized mono instances of local poly decls, awaiting insertion into enclosing Where.
  }

makeLenses ''State

emptyState :: State
emptyState = State
  { _instances         = Map.empty
  , _exportedDecls     = []
  , _sourceDecls       = Map.empty
  , _sourceDataDecls   = Map.empty
  , _conToDataType     = Map.empty
  , _localSourceDecls  = Map.empty
  , _localPendingDecls = []
  }
