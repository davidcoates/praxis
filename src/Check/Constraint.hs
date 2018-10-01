{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances  #-}

module Check.Constraint
  ( Constraint(..)
  , Derivation(..)
  , Reason(..)
  , newDerivation
  , share
  , implies
  ) where

import           Common
import           Source     (Source)
import           Tag        (Tag (..))
import           Type

import           Data.Maybe (fromMaybe)
import           Prelude    hiding (drop)

data Constraint = Class (Kinded Type)
                | EqType (Kinded Type) (Kinded Type)
                | EqKind Kind Kind
                | Generalises (Kinded QType) (Kinded Type)
                | Specialises (Kinded Type) (Kinded QType)
  deriving (Eq, Ord)

instance Show Constraint where
  show (Class t)         = show t
  show (EqType t1 t2)    = show t1 ++ " ~ " ++ show t2
  show (EqKind k1 k2)    = show k1 ++ " ~ " ++ show k2 -- TODO need this?
  show (Generalises q t) = show q ++ " >> " ++ show t
  show (Specialises t q) = show t ++ " < " ++ show q

data Reason = AppFun
            | AppType
            | Captured Name
            | CaseCongruence
            | Custom String
            | Generalisation Name
            | IfCondition
            | IfCongruence
            | Instance Name
            | Shared Name
            | Specialisation
            | Unknown -- TODO eventually get rid of this
            | UnsafeView Name
            | UserSignature (Maybe Name)

instance Show Reason where
  show r = case r of
    AppFun           -> "Function application"
    AppType          -> "Type application"
    Captured n       -> "Variable '" ++ n ++ "' captured"
    CaseCongruence   -> "Alternatives of <case> expression must have the same type"
    Custom s         -> s
    Generalisation n -> "Generalised type of '" ++ n ++ "'"
    IfCondition      -> "Type of <if> condition must be Bool"
    IfCongruence     -> "Branches of <if> expression must have the same type"
    Instance n       -> "Monomorphic usage of '" ++ n ++ "'"
    Shared n         -> "Variable '" ++ n ++ "' used more than once"
    Specialisation   -> "Specialisation"
    Unknown          -> "<Unknown>"
    UserSignature n  | Just f <- n -> "User-supplied signature '" ++ f ++ "'"
                     | otherwise   -> "User-supplied signature"
    UnsafeView n     -> "Variable '" ++ n ++ "' used before being viewed"


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

instance PseudoTraversable (Kinded Type) (Kinded Type) Constraint Constraint where
  pseudoTraverse f c = case c of
    Class t         -> Class <$> pseudoTraverse f t
    EqType t1 t2    -> EqType <$> pseudoTraverse f t1 <*> pseudoTraverse f t2
    EqKind _ _      -> pure c
    Generalises q t -> Generalises <$> pseudoTraverse f q <*> pseudoTraverse f t
    Specialises t q -> Specialises <$> pseudoTraverse f t <*> pseudoTraverse f q

instance PseudoTraversable Kind Kind Constraint Constraint where
  pseudoTraverse f c = case c of
    Class t         -> Class <$> pseudoTraverse f t
    EqType t1 t2    -> EqType <$> pseudoTraverse f t1 <*> pseudoTraverse f t2
    EqKind k1 k2    -> EqKind <$> pseudoTraverse f k1 <*> pseudoTraverse f k2
    Generalises q t -> Generalises <$> pseudoTraverse f q <*> pseudoTraverse f t
    Specialises t q -> Specialises <$> pseudoTraverse f t <*> pseudoTraverse f q

instance PseudoTraversable (Kinded QType) (Kinded QType) Constraint Constraint where
  pseudoTraverse f c = case c of
    Generalises q t -> Generalises <$> f q <*> pure t
    Specialises t q -> Specialises <$> pure t <*> f q
    _               -> pure c

instance PseudoTraversable a a Constraint Constraint => PseudoTraversable a a Derivation Derivation where
  pseudoTraverse f c = (\x y -> c{ constraint = x, original = y }) <$> pseudoTraverse f (constraint c) <*> pseudoTraverse f (original c)

