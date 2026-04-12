{-# LANGUAGE TemplateHaskell #-}

module Check.State
  ( Constraint(..)
  , Constraints(..)
  , requirements
  , assumptions
  , emptyConstraints

  , TypeConEnv(..)
  , TypeVarEnv(..)
  , KindState(..)
  , typeConEnv

  , ConEnv(..)
  , VarEnv(..)
  , InbuiltEnv(..)
  , Usage(..)
  , usedCount
  , readCount
  , TypeState(..)
  , conEnv
  , varEnv
  , inbuiltEnv
  , varRename
  , globalVars

  , InstanceOrigin(..)
  , Instance(..)
  , InstanceEnv(..)
  , State(..)
  , kindState
  , typeState
  , instanceEnv

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


type family Constraint (s :: Stage) where
  Constraint TypeCheck = TypeConstraint
  Constraint KindCheck = KindConstraint

data Constraints (s :: Stage) = Constraints
  { _requirements :: Set (Annotated s (Requirement (Constraint s)))
  , _assumptions  :: Set (Annotated s (Constraint s))
  }

makeLenses ''Constraints

emptyConstraints :: Ord (Annotated s (Constraint s)) => Constraints s
emptyConstraints = Constraints
  { _requirements = Set.empty
  , _assumptions  = Set.empty
  }

type TypeConEnv = Map Name (Annotated KindCheck Kind) -- ^ Type constructor environment

type TypeVarEnv = Map Name (Flavor, Annotated KindCheck Kind) -- ^ Type variable environment

data KindState = KindState
  { _typeConEnv :: TypeConEnv
  }

makeLenses ''KindState

emptyKindState :: KindState
emptyKindState = KindState
  { _typeConEnv = Map.empty
  }

type ConEnv = Map Name (Annotated TypeCheck QType) -- ^ Constructor environment

data Usage = Usage { _usedCount :: Int, _readCount :: Int }

makeLenses ''Usage

instance Semigroup Usage where
  u1 <> u2 = Usage { _usedCount = max (view usedCount u1) (view usedCount u2), _readCount = max (view readCount u1) (view readCount u2) }

instance Monoid Usage where
  mempty = Usage { _usedCount = 0, _readCount = 0 }

type VarEnv = Map Name (Usage, Annotated TypeCheck QType) -- ^ Variable environment

type InbuiltEnv = Map Name (Inbuilt, Annotated TypeCheck QType) -- ^ Inbuilt environment

data TypeState = TypeState
  { _conEnv     :: ConEnv
  , _varEnv     :: VarEnv
  , _inbuiltEnv :: InbuiltEnv
  , _varRename  :: Map Name Name
  , _globalVars :: Set Name
  }

makeLenses ''TypeState

emptyTypeState :: TypeState
emptyTypeState = TypeState
  { _conEnv     = Map.empty
  , _varEnv     = Map.empty
  , _inbuiltEnv = Map.empty
  , _varRename  = Map.empty
  , _globalVars = Set.empty
  }

data InstanceOrigin = Native | Trivial
  deriving Eq

data Instance = IsInstance | IsInstanceOnlyIf [Annotated TypeCheck TypeConstraint]

type InstanceEnv = Map Name (Map TypeInstance ([Annotated TypeCheck Type] -> (InstanceOrigin, Instance))) -- ^ Instance environment

data State = State
  { _kindState   :: KindState
  , _typeState   :: TypeState
  , _instanceEnv :: InstanceEnv
  }

makeLenses ''State

emptyState :: State
emptyState = State
  { _kindState = emptyKindState
  , _typeState = emptyTypeState
  , _instanceEnv = Map.empty
  }
