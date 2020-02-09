{-# LANGUAGE OverloadedStrings #-}

module Check.Type.Error
  ( Error(..)
  ) where

import           Common
import           Print
import           Term

data Error = Contradiction (Annotated TypeConstraint)
           | ShareAffine (Annotated Type)
           | Underdefined (Annotated TypeConstraint)
           | Stuck

instance Pretty Error where
  pretty = \case
    Contradiction c -> "found contradiction " <> pretty c
    ShareAffine t   -> "deduced Share " <> pretty t <> " and Affine " <> pretty t
    Stuck           -> "infinite loop detected :("
    Underdefined c  -> "failed to completely deduce the unification variable(s) present in " <> pretty c
