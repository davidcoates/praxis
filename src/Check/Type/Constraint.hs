{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances  #-}

module Check.Type.Constraint
  ( Constraint(..)
  , Derivation(..)
  , Reason(..)
  ) where

import           Annotate
import           Common
import           Source
import           Stage      (TypeCheck)
import           Type

import           Data.Maybe (fromMaybe)
import           Prelude    hiding (drop)

type Typed a = Annotated TypeCheck a

data Constraint = Class (Typed Type)
                | Eq (Typed Type) (Typed Type)
                | Generalises (Typed QType) (Typed Type)
                | Specialises (Typed Type) (Typed QType)
  deriving (Eq, Ord)

{-
instance Show Constraint where
  show (Class t)         = show t
  show (Eq t1 t2)    = show t1 ++ " ~ " ++ show t2
  show (Generalises q t) = show q ++ " >> " ++ show t
  show (Specialises t q) = show t ++ " < " ++ show q
-}

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

data Derivation = Derivation { origin :: Constraint, reason :: Reason }

{-
instance Show Derivation where
  show c = "derived from: " ++ show (origin c) ++ "; reason: " ++ show (reason c)
-}

