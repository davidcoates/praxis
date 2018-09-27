{-# LANGUAGE RankNTypes      #-}
{-# LANGUAGE TemplateHaskell #-}

module Check.System
  ( System
  , initialSystem

  -- |System lenses
  , axioms
  , changed
  , constraints
  , tySol
  , kindSol
  , staging
  ) where

import           Check.Constraint (Constraint, Derivation)
import           Common           (Name)
import           Type             (Kind, Kinded, Type)

import           Control.Lens     (makeLenses)

initialSystem :: System
initialSystem = System
  { _tySol       = []
  , _kindSol     = []
  , _constraints = []
  , _axioms      = []
  , _changed     = False
  , _staging     = []
  }

data System = System
  { _tySol       :: [(Name, Kinded Type)]
  , _kindSol     :: [(Name, Kind)]
  , _constraints :: [Derivation]
  , _staging     :: [Derivation]
  , _axioms      :: [Constraint]
  , _changed     :: Bool
  } deriving (Show)

makeLenses ''System
