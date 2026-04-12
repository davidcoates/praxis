{-# LANGUAGE TemplateHaskell #-}

module Lower.State
  ( State(..)
  , specializations
  , polyDecls
  , polyDataDecls
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
  { _specializations :: Map (Name, [Annotated TypeCheck Type]) Name
  -- ^ Maps (original polymorphic name, concrete type args) to the generated monomorphic name.
  , _polyDecls       :: Map Name (Annotated TypeCheck DeclTerm)
  -- ^ Source definitions of top-level polymorphic functions, for on-demand specialization.
  , _polyDataDecls   :: Map Name (Annotated TypeCheck DeclType)
  -- ^ Polymorphic DeclTypeData declarations keyed by data type name.
  , _conToDataType   :: Map Name Name
  -- ^ Maps each constructor name to its owning data type name.
  }

makeLenses ''State

emptyState :: State
emptyState = State
  { _specializations = Map.empty
  , _polyDecls       = Map.empty
  , _polyDataDecls   = Map.empty
  , _conToDataType   = Map.empty
  }
