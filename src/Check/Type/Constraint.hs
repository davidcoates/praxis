{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE UndecidableInstances #-}

module Check.Type.Constraint
  ( TypeConstraint(..)
  , Derivation(..)
  , Reason(..)
  ) where

import           Common
import           Stage      (TypeCheck)
import           Type

import           Data.Maybe (fromMaybe)
import           Prelude    hiding (drop)

-- The parameter is only to allow introspection, we always expect it to be TypeCheck
data TypeConstraint a = Class (Annotated a Type)
                      | Eq (Annotated a Type) (Annotated a Type)
                      | Generalises (Annotated a QType) (Annotated a Type)
                      | Specialises (Annotated a Type) (Annotated a QType)
  deriving (Eq, Ord)

data Reason = AppFun
            | Captured Name
            | CaseCongruence
            | Custom String
            | Generalisation Name
            | IfCondition
            | IfCongruence
            | Instance Name
            | Shared Name
            | Specialisation
            | Unknown
            | UnsafeView Name
            | UserSignature (Maybe Name)

instance Show Reason where
  show r = case r of
    AppFun           -> "Function application"
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

data Derivation = Root Reason
                | Antecedent (Annotated TypeCheck TypeConstraint)

instance Show (Annotated TypeCheck TypeConstraint) => Show Derivation where
  show (Root r)       = "\n|-> (" ++ show r ++ ")"
  show (Antecedent a) =  "\n|-> " ++ show a
