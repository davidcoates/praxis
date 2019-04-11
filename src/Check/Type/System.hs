{-# LANGUAGE TemplateHaskell #-}

module Check.Type.System
  ( System
  , tsol
  , constraints
  , staging
  , axioms

  , initialSystem
  ) where

import           Check.Type.Annotate
import           Check.Type.Constraint
import           Common
import           Stage
import           Type                  (Type)

data System = System
  { _tsol        :: [(Name, Type TypeCheck)]
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
