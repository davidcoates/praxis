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

import           Check.Kind.Annotate
import           Check.Kind.Constraint
import           Common
import           Type                  (Kind)

data System = System
  { _sol         :: [(Name, Kind)]
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