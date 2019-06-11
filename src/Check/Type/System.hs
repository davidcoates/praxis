{-# LANGUAGE TemplateHaskell #-}

module Check.Type.System
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
  { _sol         :: [(Name, Type TypeAnn)]
  , _constraints :: [Typed TypeConstraint]
  , _staging     :: [Typed TypeConstraint]
  , _axioms      :: [Typed TypeConstraint]
  }

makeLenses ''System

initialSystem :: System
initialSystem = System
  { _sol        = []
  , _constraints = []
  , _staging     = []
  , _axioms      = []
  }
