{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE UndecidableInstances  #-}

module Check.Kind.Constraint
  ( Constraint(..)
  , Derivation(..)
  , Reason(..)
  , origin
  , reason
  ) where

import           Common
import           Control.Lens (makeLenses)
import           Source
import           Tag
import           Type

data Constraint = Eq Kind Kind
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
  { _origin :: Constraint
  , _reason :: Reason }

makeLenses ''Derivation

{-
instance Show Derivation where
  show c = "derived from: " ++ show (origin c) ++ "; reason: " ++ show (reason c)
-}
