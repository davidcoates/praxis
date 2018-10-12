{-# LANGUAGE TemplateHaskell #-}

module Check.Type.System
  ( System
  , sol
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

type C = Typed (Const Constraint) -- For some reason makeLenses complains when trying to use the RHS directly

data System = System
  { _sol         :: [(Name, Typed Type)]
  , _qsol        :: [(Name, Typed QType)]
  , _constraints :: [C]
  , _staging     :: [C]
  , _axioms      :: [C]
  }

makeLenses ''System

initialSystem :: System
initialSystem = System
  { _sol         = []
  , _qsol        = []
  , _constraints = []
  , _staging     = []
  , _axioms      = []
  }
