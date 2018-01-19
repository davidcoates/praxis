module Checker.Constraint
  ( Constraint(..)
  , TConstraint(..)
  , share
  , drop
  , subsConstraint
  , newTConstraint
  , implies
  ) where

import Prelude hiding (drop)
import Type hiding (Constraint(..))
import qualified Type as Class (Constraint(..))
import AST (SourcePos(..))

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

data TConstraint = TConstraint { constraint :: Constraint, original :: Constraint, cause :: String, position :: SourcePos }

verbose :: TConstraint -> String
verbose c = "\n(" ++ show (constraint c) ++ " derived from " ++ show (original c) ++ ", generator reason: " ++ show (cause c) ++ ")"

instance Show TConstraint where
  show c@TConstraint { constraint = Sub a b } = "\nExpected " ++ show b ++ ", actual type " ++ show a ++ verbose c
  show c = verbose c

newTConstraint :: Constraint -> String -> SourcePos -> TConstraint
newTConstraint c s p = TConstraint { constraint = c, original = c, cause = s, position = p }

implies :: TConstraint -> Constraint -> TConstraint
implies c c' = c { constraint = c' }
