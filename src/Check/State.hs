{-# LANGUAGE TemplateHaskell  #-}

module Check.State
  ( Constraint(..)
  , SolveState(..)
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

data SolveState (s :: Stage) = SolveState
  { _requirements :: Set (Annotated s (Requirement (Constraint s)))
  , _assumptions  :: Set (Annotated s (Constraint s))
  }

makeLenses ''SolveState

emptySolveState :: Ord (Annotated s (Constraint s)) => SolveState s
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

type TypeConEnv = Map Name (Annotated KindCheck Kind) -- ^ Type constructor environment

type TypeVarEnv = Map Name (Flavor, Annotated KindCheck Kind) -- ^ Type variable environment

data KindState = KindState
  { _kindSolve     :: SolveState KindCheck
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

type ConEnv = Map Name (Annotated TypeCheck QType) -- ^ Constructor environment

data Usage = Usage { _usedCount :: Int, _readCount :: Int }

makeLenses ''Usage

instance Semigroup Usage where
  u1 <> u2 = Usage { _usedCount = max (view usedCount u1) (view usedCount u2), _readCount = max (view readCount u1) (view readCount u2) }

instance Monoid Usage where
  mempty = Usage { _usedCount = 0, _readCount = 0 }

type VarEnv = Map Name (Usage, Annotated TypeCheck QType) -- ^ Variable environment

data TypeState = TypeState
  { _typeSolve :: SolveState TypeCheck
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

data Instance = IsInstance | IsInstanceOnlyIf [Annotated TypeCheck TypeConstraint]

type InstanceEnv = Map Name (Map Name ([Annotated TypeCheck Type] -> (InstanceOrigin, Instance))) -- ^ Instance environment

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
