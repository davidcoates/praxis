module Check.Derivation
  ( Derivation(..)
  , newDerivation
  , equalI
  , implies
  , showDerivation
  ) where

import           Prelude hiding (drop)
import           Source  (Source)
import           Type

-- |A Derivation represents a constraint with a history of why the constraint must be true.
-- 'original' is the constraint that 'constraint' was ultimately derived from.
data Derivation = Derivation { constraint :: Constraint, original :: Constraint, cause :: String, source :: Source }

showDerivation :: Derivation -> String
showDerivation c = show (constraint c) ++ " derived from " ++ show (original c) ++ ", generator reason: " ++ show (cause c)

instance Show Derivation where
  show c = show (constraint c)

newDerivation :: Constraint -> String -> Source -> Derivation
newDerivation c s a = Derivation { constraint = c, original = c, cause = s, source = a }

equalI :: Impure -> Impure -> String -> Source -> [Derivation]
equalI (p1 :# e1) (p2 :# e2) s a = [ newDerivation (EqualP p1 p2) s a, newDerivation (EqualE e1 e2) s a ]

implies :: Derivation -> Constraint -> Derivation
implies c c' = c { constraint = c' }
