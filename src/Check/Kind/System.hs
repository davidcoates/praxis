{-# LANGUAGE TemplateHaskell #-}

module Check.Kind.System
  ( System
  , sol
  , constraints

  , initialSystem
  ) where

import           Common
import           Term

data System = System
  { _sol         :: [(Name, Kind)]
  , _constraints :: [Annotated KindProp]
  }

makeLenses ''System

initialSystem :: System
initialSystem = System
  { _sol         = []
  , _constraints = []
  }
