module Check.Derivation
  ( Derivation(..)
  , newDerivation
  , implies
  ) where

import Prelude hiding (drop)
import Type
import Source (Source)

-- |A Derivation represents a constraint with a history of why the constraint must be true.
-- 'original' is the constraint that 'constraint' was ultimately derived from.
data Derivation = Derivation { constraint :: Constraint, original :: Constraint, cause :: String, source :: Source }

showDerivation :: Derivation -> String
showDerivation c = show (constraint c) ++ " derived from " ++ show (original c) ++ ", generator reason: " ++ show (cause c)

instance Show Derivation where
  show c = show (constraint c)

newDerivation :: Constraint -> String -> Source -> Derivation
newDerivation c s a = Derivation { constraint = c, original = c, cause = s, source = a }

implies :: Derivation -> Constraint -> Derivation
implies c c' = c { constraint = c' }
