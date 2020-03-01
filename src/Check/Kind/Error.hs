{-# LANGUAGE OverloadedStrings #-}

module Check.Kind.Error
  ( Error(..)
  ) where

import           Common
import           Pretty
import           Print
import           Term

data Error = Contradiction (Annotated KindConstraint)
           | Stuck

instance Pretty Error where
  pretty = \case
    Contradiction c -> "found contradiction " <> pretty c
    Stuck           -> "infinite loop detected :("
