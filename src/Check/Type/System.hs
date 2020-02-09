{-# LANGUAGE TemplateHaskell #-}

module Check.Type.System
  ( System
  , sol
  , ops
  , constraints
  , staging
  , axioms

  , initialSystem
  ) where

import           Common
import           Term

data System = System
  { _sol         :: [(Name, Type)]
  , _ops         :: [(Name, TyOp)]
  , _constraints :: [Annotated TypeConstraint]
  , _staging     :: [Annotated TypeConstraint]
  , _axioms      :: [Annotated TypeConstraint]
  }

makeLenses ''System

initialSystem :: System
initialSystem = System
  { _sol         = []
  , _ops         = []
  , _constraints = []
  , _staging     = []
  , _axioms      = []
  }
