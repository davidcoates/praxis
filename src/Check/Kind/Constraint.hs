{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE UndecidableInstances #-}

module Check.Kind.Constraint
  ( KindConstraint(..)
  , Derivation(..)
  , Reason(..)
  ) where

import           Common
import           Stage  (KindCheck)
import           Type

data KindConstraint a = Eq (Annotated a Kind) (Annotated a Kind)
  deriving (Eq, Ord)

data Reason = AppType
            | Custom String -- TODO get rid of Custom and Unknown
            | Unknown

instance Show Reason where
  show r = case r of
    AppType  -> "Type application"
    Custom s -> s
    Unknown  -> "<Unknown>"

data Derivation = Root Reason
                | Antecedent (Annotated KindCheck KindConstraint)

instance Show (Annotated KindCheck KindConstraint) => Show Derivation where
  show (Root r)       = "\n|-> (" ++ show r ++ ")"
  show (Antecedent a) =  "\n|-> " ++ show a
