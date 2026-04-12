{-# LANGUAGE TemplateHaskell #-}

module Check.Kind.State
  ( KindLocal
  , kindSolveLocal
  , typeVarEnvLocal
  , typeVarRenameLocal
  , emptyKindLocal
  , KindM
  ) where

import           Check.State         (Constraints, TypeVarEnv, emptyConstraints)
import           Common              (Name, makeLenses)
import           Control.Monad.State (StateT)
import           Praxis              (Praxis)
import           Stage

import           Data.Map.Strict     (Map)
import qualified Data.Map.Strict     as Map


data KindLocal = KindLocal
  { _kindSolveLocal     :: Constraints KindCheck
  , _typeVarEnvLocal    :: TypeVarEnv
  , _typeVarRenameLocal :: Map Name Name
  }

makeLenses ''KindLocal

emptyKindLocal :: KindLocal
emptyKindLocal = KindLocal
  { _kindSolveLocal     = emptyConstraints
  , _typeVarEnvLocal    = Map.empty
  , _typeVarRenameLocal = Map.empty
  }

-- | The kind-checking monad: local kind state layered over Praxis.
type KindM = StateT KindLocal Praxis
