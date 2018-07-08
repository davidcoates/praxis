{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Check.Constraint
  ( Constraint(..)
  , Derivation(..)
  , Reason(..)
  , newDerivation
  , share
  , implies
  ) where

import           Prelude             hiding (drop)
import           Source              (Source)
import           Tag                 (Tag (..))
import           Type

import           Control.Applicative (liftA2)
import           Data.Maybe          (fromMaybe)

data Constraint = Class (Kinded Type)
                | EqType (Kinded Type) (Kinded Type)
                | EqKind Kind Kind
  deriving (Eq, Ord)

instance Show Constraint where
  show (Class t)      = show t
  show (EqType t1 t2) = show t1 ++ " ~ "  ++ show t2 -- TODO have a way of showing types without annotations ?
  show (EqKind k1 k2) = show k1 ++ " ~ "  ++ show k2 -- TODO need this?

data Reason = AppFun
            | AppType
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
  show AppFun            = "Function application"
  show AppType           = "Type application"
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
  d1 == d2 = constraint d1 == constraint d2

instance Ord Derivation where
  d1 `compare` d2 = constraint d1 `compare` constraint d2

instance Show Derivation where
  show c = show (constraint c) ++ " derived from " ++ show (original c) ++ ". Reason: " ++ show (reason c) ++ " @ " ++ show (source c)

newDerivation :: Constraint -> Reason -> Source -> Derivation
newDerivation c r s = Derivation { constraint = c, original = c, reason = r, source = s }

share :: Kinded Type -> Constraint
share t = Class $ KindConstraint :< TyApply (KindFun KindType KindConstraint :< TyCon "Share") t

implies :: Derivation -> Constraint -> Derivation
implies c c' = c { constraint = c' }

instance TypeTraversable Constraint where
  typeTraverse f c = case c of
    Class t      -> Class <$> typeTraverse f t
    EqType t1 t2 -> liftA2 EqType (typeTraverse f t1) (typeTraverse f t2)
    _            -> pure c

instance KindTraversable Constraint where
  kindTraverse f c = case c of
    EqType t1 t2 -> liftA2 EqType (kindTraverse f t1) (kindTraverse f t2)
    EqKind k1 k2 -> liftA2 EqKind (kindTraverse f k1) (kindTraverse f k2)
    _            -> pure c

instance TypeTraversable Derivation where
  typeTraverse f c = (\x -> c{ constraint = x}) <$> typeTraverse f (constraint c)

instance KindTraversable Derivation where
  kindTraverse f c = (\x -> c{ constraint = x}) <$> kindTraverse f (constraint c)
