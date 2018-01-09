module Checker.Constraint 
  ( Constraint(..)
  , share
  , drop
  ) where

import Prelude hiding (drop)
import Type hiding (Constraint(..))
import qualified Type as T (Constraint(..))

data Constraint = Top
                | Bottom
                | Eq Type Type
                | Prim T.Constraint

instance Show Constraint where
  show Top      = "⊤"
  show Bottom   = "⊥"
  show (Eq a b) = show a  ++ " ~ " ++ show b
  show (Prim c) = show c

share :: Type -> Constraint
share = Prim . T.Constraint "Share"

drop :: Type -> Constraint
drop = Prim . T.Constraint "Drop"
