{-# LANGUAGE TemplateHaskell #-}

module Check.Kind.System
  ( System
  , sol
  , constraints
  , staging
  , axioms

  , initialSystem
  ) where

import           Common
import           Term

data System = System
  { _sol         :: [(Name, Kind KindAnn)]
  , _constraints :: [Kinded KindConstraint]
  , _staging     :: [Kinded KindConstraint]
  , _axioms      :: [Kinded KindConstraint]
  }

makeLenses ''System

initialSystem :: System
initialSystem = System
  { _sol         = []
  , _constraints = []
  , _staging     = []
  , _axioms      = []
  }
