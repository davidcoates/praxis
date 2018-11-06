{-# LANGUAGE TemplateHaskell #-}

module Check.Type.System
  ( System
  , tsol
  , qsol
  , constraints
  , staging
  , axioms

  , initialSystem
  ) where

import           Check.Type.Annotate
import           Check.Type.Constraint
import           Common
import           Stage
import           Type                  (QType, Type)

data System = System
  { _tsol        :: [(Name, Type TypeCheck)]
  , _qsol        :: [(Name, QType TypeCheck)]
  , _constraints :: [Typed TypeConstraint]
  , _staging     :: [Typed TypeConstraint]
  , _axioms      :: [Typed TypeConstraint]
  }

makeLenses ''System

initialSystem :: System
initialSystem = System
  { _tsol        = []
  , _qsol        = []
  , _constraints = []
  , _staging     = []
  , _axioms      = []
  }
