module Check.Derivation
  ( Derivation(..)
  , Reason(..)
  , newDerivation
  , equalI
  , implies
  , showDerivation
  ) where

import           Prelude hiding (drop)
import           Source  (Source)
import           Sub
import           Type

data Reason = Application
            | Captured Name
            | CaseCongruence
            | Custom String
            | IfCondition
            | IfCongruence
            | Instance Name
            | Shared Name
            | Unknown -- TODO eventually get rid of this
            | UnsafeView Name
            | UserSignature (Maybe Name)

instance Show Reason where
  show Application       = "Function application"
  show (Captured n)      = "Variable '" ++ n ++ "' captured"
  show CaseCongruence    = "Alternatives of <case> expression must have the same type"
  show (Custom s)        = s
  show IfCondition       = "Type of <if> condition must be Bool"
  show IfCongruence      = "Branches of <if> expression must have the same type"
  show (Instance n)      = "Monomorphic usage of '" ++ n ++ "'"
  show (Shared n)        = "Variable '" ++ n ++ "' used more than once"
  show Unknown           = "<Unknown>"
  show (UserSignature n) | Just f <- n = "User-supplied signature '" ++ f ++ "'"
                         | otherwise   = "User-supplied signature"
  show (UnsafeView n)    = "Variable '" ++ n ++ "' used before being viewed"


-- |A Derivation represents a constraint with a history of why the constraint must be true.
-- 'original' is the constraint that 'constraint' was ultimately derived from.
data Derivation = Derivation { constraint :: Constraint, original :: Constraint, reason :: Reason, source :: Source }

instance Eq Derivation where
  d == d' = constraint d == constraint d'

instance Ord Derivation where
  d `compare` d' = constraint d `compare` constraint d'

instance Sub Derivation where
  sub f d = d { constraint = sub f (constraint d), original = sub f (original d) }

showDerivation :: Derivation -> String
showDerivation c = show (constraint c) ++ " derived from " ++ show (original c) ++ ". Reason: " ++ show (reason c) ++ " @ " ++ show (source c)

instance Show Derivation where
  show c = show (constraint c)

newDerivation :: Constraint -> Reason -> Source -> Derivation
newDerivation c r s = Derivation { constraint = c, original = c, reason = r, source = s }

equalI :: Impure -> Impure -> Reason -> Source -> [Derivation]
equalI (p1 :# e1) (p2 :# e2) r s = [ newDerivation (EqualP p1 p2) r s, newDerivation (EqualE e1 e2) r s ]

implies :: Derivation -> Constraint -> Derivation
implies c c' = c { constraint = c' }
