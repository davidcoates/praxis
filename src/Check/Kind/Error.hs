{-# LANGUAGE OverloadedStrings #-}

module Check.Kind.Error
  ( Error(..)
  ) where

import           Common
import           Print
import           Term

data Error = Contradiction (Kinded KindConstraint)
           | Stuck

instance Pretty Error where
  pretty e = case e of
    Contradiction c -> "found contradiction " <> pretty c
    Stuck           -> "infinite loop detected :("
