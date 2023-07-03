{-# LANGUAGE Rank2Types      #-}
{-# LANGUAGE TemplateHaskell #-}

module Check.Type.System
  ( Axiom(..)
  , checkAxiom

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

data Axiom = Satisfies (TyConstraint -> Maybe TyProp) | Axiom TyConstraint

data System = System
  { _sol         :: [(Name, Type)]
  , _ops         :: [(Name, TyOp)]
  , _constraints :: [Annotated TyProp]
  , _axioms      :: [Axiom]
  }

makeLenses ''System

share :: Name -> Axiom
share n = Satisfies $ \case
  Share  (_ :< TyCon m ) | m == n -> Just Top
  _                               -> Nothing

checkAxiom :: Axiom -> TyConstraint -> Maybe TyProp
checkAxiom = \case
    Satisfies f -> f
    Axiom c     -> \c' -> (if c == c' then Just Top else Nothing) -- TODO need to be smarter about this!


initialSystem :: System
initialSystem = System
  { _sol         = []
  , _ops         = []
  , _constraints = []
  , _axioms      =
    [ share "Int"
    , share "Bool"
    , share "Char"
    , Satisfies $ \case { Share (_ :< TyApply (_ :< TyCon "Parser") _) -> Just Top; _ -> Nothing } -- FIXME remove
    ]
  }
