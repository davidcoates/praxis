{-# LANGUAGE KindSignatures  #-}
{-# LANGUAGE TemplateHaskell #-}

module Check.Kind.System
  ( System
  , sol
  , constraints
  , staging
  , axioms

  , initialSystem
  ) where

import           Control.Lens          (makeLenses)

import           Check.Kind.Annotate
import           Check.Kind.Constraint
import           Common
import           Tag
import           Type                  (Kind)

data System = System
  { _sol         :: [(Name, Kind)]
  , _constraints :: [Kinded (Const Constraint)]
  , _staging     :: [Kinded (Const Constraint)]
  , _axioms      :: [Kinded (Const Constraint)]
  }

makeLenses ''System

initialSystem :: System
initialSystem = System
  { _sol         = []
  , _constraints = []
  , _staging     = []
  , _axioms      = []
  }
