{-# LANGUAGE Rank2Types      #-}
{-# LANGUAGE TemplateHaskell #-}

module Check.Type.System
  ( Axiom(..)
  , axiom

  , System
  , sol
  , ops
  , constraints
  , axioms

  , initialSystem
  ) where

import           Common
import           Introspect
import           Term

data Axiom = Axiom (TyConstraint -> Maybe TyProp)

data System = System
  { _sol         :: [(Name, Type)]
  , _ops         :: [(Name, TyOp)]
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
  { _sol         = []
  , _ops         = []
  , _constraints = []
  , _axioms      =
    [ share "Int"
    , share "Bool"
    , share "Char"
    , Axiom $ \case { Share (_ :< TyApply (_ :< TyCon "Parser") _) -> Just Top; _ -> Nothing } -- FIXME remove
    ]
  }
