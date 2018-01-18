module Checker.Constraint
  ( Constraint(..)
  , share
  , drop
  , subsConstraint
  ) where

import Prelude hiding (drop)
import Type hiding (Constraint(..))
import qualified Type as T (Constraint(..))

data Constraint = Top
                | Bottom
                | Sub Type Type
                | Prim T.Constraint

instance Show Constraint where
  show Top      = "⊤"
  show Bottom   = "⊥"
  show (Sub a b) = show a  ++ " <= " ++ show b
  show (Prim c) = show c

share :: Type -> Constraint
share = Prim . T.Constraint "Share"

drop :: Type -> Constraint
drop = Prim . T.Constraint "Drop"

subsConstraint :: (String -> Pure) -> (String -> Effects) -> Constraint -> Constraint
subsConstraint ft fe = subsC
  where subsC Top = Top
        subsC Bottom = Bottom
        subsC (Sub t1 t2) = Sub (subsT t1) (subsT t2)
        subsC (Prim (T.Constraint s t)) = Prim  (T.Constraint s (subsT t))
        subsT = subsType ft fe
