{-# LANGUAGE TemplateHaskell #-}

module Check.Type.System
  ( System
  , tsol
  , constraints
  , staging
  , axioms

  , initialSystem
  ) where

import           Common
import           Term

data System = System
  { _tsol        :: [(Name, Type TypeAnn)]
  , _constraints :: [Typed TypeConstraint]
  , _staging     :: [Typed TypeConstraint]
  , _axioms      :: [Typed TypeConstraint]
  }

makeLenses ''System

initialSystem :: System
initialSystem = System
  { _tsol        = []
  , _constraints = []
  , _staging     = []
  , _axioms      = []
  }
