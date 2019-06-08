{-# LANGUAGE StandaloneDeriving #-}

module Kind
  ( Kind(..)
  , Constraint(..)
  ) where

import {-# SOURCE #-} Annotate (Annotated)
import           Common
import           Record

data Kind a = KindUni Name
            | KindConstraint
            | KindFun (Annotated a Kind) (Annotated a Kind)
            | KindRecord (Record (Annotated a Kind))
            | KindType
  deriving (Eq, Ord)

data Constraint a = Eq (Annotated a Kind) (Annotated a Kind)
  deriving (Eq, Ord)

