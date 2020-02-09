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
  { _sol         :: [(Name, Kind)]
  , _constraints :: [Annotated KindConstraint]
  , _staging     :: [Annotated KindConstraint]
  , _axioms      :: [Annotated KindConstraint]
  }

makeLenses ''System

initialSystem :: System
initialSystem = System
  { _sol         = []
  , _constraints = []
  , _staging     = []
  , _axioms      = []
  }
