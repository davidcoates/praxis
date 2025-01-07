{-# LANGUAGE TemplateHaskell #-}

module Check.State
  ( SolveState(..)
  , requirements
  , assumptions

  , RenameState(..)
  , counts
  , renames

  , TypeConEnv(..)
  , TypeVarEnv(..)
  , KindState(..)
  , kindSolve
  , typeConEnv
  , typeVarEnv
  , typeVarRename

  , ConEnv(..)
  , VarEnv(..)
  , Usage(..)
  , usedCount
  , readCount
  , TypeState(..)
  , typeSolve
  , conEnv
  , varEnv
  , varRename

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
import           Term

import           Control.Lens    (makeLenses)
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import           Data.Set        (Set)
import qualified Data.Set        as Set


data SolveState c = SolveState
  { _requirements :: Set (Annotated (Requirement c))
  , _assumptions  :: Set c
  }

makeLenses ''SolveState

emptySolveState :: Ord c => SolveState c
emptySolveState = SolveState
  { _requirements = Set.empty
  , _assumptions  = Set.empty
  }

data RenameState = RenameState
  { _counts  :: Map Name Int
  , _renames :: Map Name Name
  }

makeLenses ''RenameState

emptyRenameState :: RenameState
emptyRenameState = RenameState
  { _counts = Map.empty
  , _renames = Map.empty
  }

type TypeConEnv = Map Name (Annotated Kind) -- ^ Type constructor environment

type TypeVarEnv = Map Name (Flavor, Annotated Kind) -- ^ Type variable environment

data KindState = KindState
  { _kindSolve     :: SolveState KindConstraint
  , _typeConEnv    :: TypeConEnv
  , _typeVarEnv    :: TypeVarEnv
  , _typeVarRename :: RenameState
  }

makeLenses ''KindState

emptyKindState :: KindState
emptyKindState = KindState
  { _kindSolve = emptySolveState
  , _typeConEnv = Map.empty
  , _typeVarEnv = Map.empty
  , _typeVarRename = emptyRenameState
  }

type ConEnv = Map Name (Annotated QType) -- ^ Constructor environment

data Usage = Usage { _usedCount :: Int, _readCount :: Int }

makeLenses ''Usage

instance Semigroup Usage where
  u1 <> u2 = Usage { _usedCount = max (view usedCount u1) (view usedCount u2), _readCount = max (view readCount u1) (view readCount u2) }

instance Monoid Usage where
  mempty = Usage { _usedCount = 0, _readCount = 0 }

type VarEnv = Map Name (Usage, Annotated QType) -- ^ Variable environment

data TypeState = TypeState
  { _typeSolve :: SolveState TypeConstraint
  , _conEnv    :: ConEnv
  , _varEnv    :: VarEnv
  , _varRename :: RenameState
  }

makeLenses ''TypeState

emptyTypeState :: TypeState
emptyTypeState = TypeState
  { _typeSolve = emptySolveState
  , _conEnv = Map.empty
  , _varEnv = Map.empty
  , _varRename = emptyRenameState
  }

data InstanceOrigin = Inbuilt | Trivial | User
  deriving Eq

data Instance = IsInstance | IsInstanceOnlyIf [TypeConstraint]

type InstanceEnv = Map Name (Map Name ([Annotated Type] -> (InstanceOrigin, Instance))) -- ^ Instance environment

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
