{-# LANGUAGE TemplateHaskell #-}

module Check.Type.System
  ( System
  , tsol
  , constraints
  , staging
  , axioms

  , initialSystem
  ) where

import           Annotate
import           Common
import           Type

data System = System
  { _tsol        :: [(Name, Type TypeCheck)]
  , _constraints :: [Typed Constraint]
  , _staging     :: [Typed Constraint]
  , _axioms      :: [Typed Constraint]
  }

makeLenses ''System

initialSystem :: System
initialSystem = System
  { _tsol        = []
  , _constraints = []
  , _staging     = []
  , _axioms      = []
  }
