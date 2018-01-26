module Check.Derivation
  ( Derivation(..)
  , newDerivation
  , implies
  ) where

import Prelude hiding (drop)
import Type
import Pos

-- ^ A Derivation represents a constraint with a history of why the constraint must be true.
-- ^ 'original' is the constraint that 'constraint' was ultimately derived from.
data Derivation = Derivation { constraint :: Constraint, original :: Constraint, cause :: String, position :: Pos }

verbose :: Derivation -> String
verbose c = "\n(" ++ show (constraint c) ++ " derived from " ++ show (original c) ++ ", generator reason: " ++ show (cause c) ++ ")"

instance Show Derivation where
  show c@Derivation { constraint = Sub a b } = "\nExpected " ++ show b ++ ", actual type " ++ show a ++ verbose c
  show c = verbose c

newDerivation :: Constraint -> String -> Pos -> Derivation
newDerivation c s p = Derivation { constraint = c, original = c, cause = s, position = p }

implies :: Derivation -> Constraint -> Derivation
implies c c' = c { constraint = c' }
