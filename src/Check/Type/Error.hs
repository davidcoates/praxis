{-# LANGUAGE OverloadedStrings #-}

module Check.Type.Error
  ( Error(..)
  ) where

import           Common
import           Print
import           Term

data Error = Contradiction (Typed TypeConstraint)
           | Stuck
           | Underdefined (Typed TypeConstraint)

instance Pretty Error where
  pretty e = case e of
    Contradiction c -> "found contradiction " <> pretty c
    Stuck           -> "infinite loop detected :("
    Underdefined c  -> "failed to completely deduce the unification variable(s) present in " <> pretty c
