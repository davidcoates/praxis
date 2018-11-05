{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE UndecidableInstances  #-}

module Check.Kind.Constraint
  ( KindConstraint(..)
  , Derivation(..)
  , Reason(..)
  , antecedent
  , reason
  ) where

import           Common
import           Control.Lens (makeLenses)
import           Stage        (KindCheck)
import           Type

-- The parameter is only to allow introspection, we always expect it to be KindCheck
data KindConstraint a = Eq Kind Kind
  deriving (Eq, Ord)

data Reason = AppType
            | Custom String -- TODO get rid of Custom and Unknown
            | Unknown

instance Show Reason where
  show r = case r of
    AppType  -> "Type application"
    Custom s -> s
    Unknown  -> "<Unknown>"

data Derivation = Derivation
  { _antecedent :: Maybe (Annotated KindCheck KindConstraint)
  , _reason     :: Reason }

makeLenses ''Derivation

{-
instance Show Derivation where
  show c = "derived from: " ++ show (origin c) ++ "; reason: " ++ show (reason c)
-}
