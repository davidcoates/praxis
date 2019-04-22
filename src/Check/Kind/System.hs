{-# LANGUAGE TemplateHaskell #-}

module Check.Kind.System
  ( System
  , sol
  , constraints
  , staging
  , axioms

  , initialSystem
  ) where

import           Annotate
import           Common
import           Kind

data System = System
  { _sol         :: [(Name, Kind KindCheck)]
  , _constraints :: [Kinded Constraint]
  , _staging     :: [Kinded Constraint]
  , _axioms      :: [Kinded Constraint]
  }

makeLenses ''System

initialSystem :: System
initialSystem = System
  { _sol         = []
  , _constraints = []
  , _staging     = []
  , _axioms      = []
  }
