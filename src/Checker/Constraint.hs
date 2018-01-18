module Checker.Constraint
  ( Constraint(..)
  , share
  , drop
  , subsConstraint
  ) where

import Prelude hiding (drop)
import Type hiding (Constraint(..))
import qualified Type as Class (Constraint(..))

data Constraint = Top
                | Bottom
                | Sub Type Type
                | Class Class.Constraint

instance Show Constraint where
  show Top      = "⊤"
  show Bottom   = "⊥"
  show (Sub a b) = show a  ++ " <= " ++ show b
  show (Class c) = show c

share :: Type -> Constraint
share = Class . Class.Constraint "Share"

drop :: Type -> Constraint
drop = Class . Class.Constraint "Drop"

subsConstraint :: (String -> Maybe Pure) -> (String -> Maybe Effects) -> Constraint -> Constraint
subsConstraint ft fe = subsC
  where subsC Top = Top
        subsC Bottom = Bottom
        subsC (Sub t1 t2) = Sub (subsT t1) (subsT t2)
        subsC (Class (Class.Constraint s t)) = Class (Class.Constraint s (subsT t))
        subsT = subsType ft fe
