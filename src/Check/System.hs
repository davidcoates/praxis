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

import           Check.Derivation (Derivation)
import           Common           (Name)
import           Type             (Constraint, Term)

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
  { _solution    :: [(Name, Term)]
  , _constraints :: [Derivation]
  , _staging     :: [Derivation]
  , _axioms      :: [Constraint]
  , _changed     :: Bool
  } deriving (Show)

makeLenses ''System
