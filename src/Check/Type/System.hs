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

import           Control.Lens          (makeLenses)

import           Check.Type.Annotate
import           Check.Type.Constraint
import           Common
import           Source
import           Tag
import           Type                  (QType, Type)

data System = System
  { _tsol        :: [(Name, Typed Type)]
  , _qsol        :: [(Name, Typed QType)]
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
