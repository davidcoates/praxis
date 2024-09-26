{-# LANGUAGE TemplateHaskell #-}

module Check.State
  ( SolveState(..)
  , requirements
  , assumptions

  , RenameState(..)
  , counts
  , scopes

  , KEnv(..)
  , KindState(..)
  , kindRename
  , kindSolve
  , kEnv

  , CEnv(..)
  , TEnv(..)
  , TypeState(..)
  , typeRename
  , typeSolve
  , cEnv
  , tEnv

  , InstanceOrigin(..)
  , Instance(..)
  , IEnv(..)
  , State(..)
  , kindState
  , typeState
  , iEnv

  , emptyState
  ) where

import           Common
import qualified Env.Linear
import qualified Env.Strict
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

data RenameState = RenameState
  { _counts :: Map Name Int
  , _scopes :: Map Name (Flavor, Int)
  }

makeLenses ''RenameState


type KEnv = Env.Strict.Env (Annotated Kind) -- ^ Kind environment

data KindState = KindState
  { _kindRename :: RenameState
  , _kindSolve  :: SolveState KindConstraint
  , _kEnv       :: KEnv
  }

makeLenses ''KindState

type CEnv = Env.Strict.Env (Annotated QType) -- ^ Constructor environment

type TEnv = Env.Linear.Env (Annotated QType) -- ^ Type environment

data TypeState = TypeState
  { _typeRename :: RenameState
  , _typeSolve  :: SolveState TypeConstraint
  , _cEnv       :: CEnv
  , _tEnv       :: TEnv
  }

makeLenses ''TypeState


data InstanceOrigin = Inbuilt | Trivial | User
  deriving Eq

data Instance = IsInstance | IsInstanceOnlyIf [TypeConstraint]

type IEnv = Env.Strict.Env (Map Name ([Annotated Type] -> (InstanceOrigin, Instance))) -- ^ Instance environment

data State = State
  { _kindState :: KindState
  , _typeState :: TypeState
  , _iEnv      :: IEnv
  }

makeLenses ''State

emptyState :: State
emptyState = State
  { _kindState = KindState
    { _kindRename = RenameState
      { _counts = Map.empty
      , _scopes = Map.empty
      }
    , _kindSolve = SolveState
      { _requirements = Set.empty
      , _assumptions  = Set.empty
      }
    , _kEnv = Env.Strict.empty
    }
  , _typeState = TypeState
    { _typeRename = RenameState
      { _counts = Map.empty
      , _scopes = Map.empty
      }
    , _typeSolve = SolveState
      { _requirements = Set.empty
      , _assumptions  = Set.empty
      }
    , _cEnv = Env.Strict.empty
    , _tEnv = Env.Linear.empty
    }
  , _iEnv = Env.Strict.empty
  }
