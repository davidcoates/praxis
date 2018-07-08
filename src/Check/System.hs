{-# LANGUAGE RankNTypes      #-}
{-# LANGUAGE TemplateHaskell #-}

module Check.System
  ( System
  , initialSystem

  -- |System lenses
  , axioms
  , changed
  , constraints
  , solution
  , staging
  ) where

import           Check.Constraint (Constraint, Derivation)
import           Common           (Name)
import           Type             (Kinded, Type)

import           Control.Lens     (makeLenses)

initialSystem :: [Derivation] -> System
initialSystem cs = System
  { _solution    = []
  , _constraints = cs
  , _axioms      = []
  , _changed     = False
  , _staging     = []
  }

data System = System
  { _solution    :: [(Name, Kinded Type)]
  , _constraints :: [Derivation]
  , _staging     :: [Derivation]
  , _axioms      :: [Constraint]
  , _changed     :: Bool
  } deriving (Show)

makeLenses ''System
