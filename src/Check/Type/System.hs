{-# LANGUAGE Rank2Types      #-}
{-# LANGUAGE TemplateHaskell #-}

module Check.Type.System
  ( Axiom(..)
  , axiom

  , Solution
  , tySol
  , viewSol

  , System
  , sol
  , constraints
  , axioms

  , initialSystem
  ) where

import           Common
import           Introspect
import           Term

data Axiom = Axiom (TyConstraint -> Maybe TyProp)

data Solution = Solution { _tySol :: [(Name, Type)], _viewSol :: [(Name, View)] }

makeLenses ''Solution

data System = System
  { _sol         :: Solution
  , _constraints :: [Annotated TyProp]
  , _axioms      :: [Axiom]
  }

makeLenses ''System

share :: Name -> Axiom
share n = Axiom $ \case
  Share  (_ :< TyCon m ) | m == n -> Just Top
  _                               -> Nothing

axiom :: TyConstraint -> Axiom
axiom c = Axiom $ \c' -> if c == c' then Just Top else Nothing

initialSystem :: System
initialSystem = System
  { _sol         = Solution { _tySol = [], _viewSol = [] }
  , _constraints = []
  , _axioms      =
    [ share "Int"
    , share "Bool"
    , share "Char"
    ]
  }
