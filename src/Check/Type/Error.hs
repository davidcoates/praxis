{-# LANGUAGE OverloadedStrings #-}

module Check.Type.Error
  ( Error(..)
  ) where

import           Annotate
import           Common
import           Type

data Error = Contradiction (Typed Constraint)
           | Stuck
           | Underdefined (Typed Constraint)

instance Pretty Error where
  pretty e = case e of
    Contradiction c -> "Contradiction: " <> pretty c
    Stuck           -> "Infinite loop detected :("
    Underdefined c  -> "Failed to completely deduce the unification variable(s) present in: " <> pretty c
