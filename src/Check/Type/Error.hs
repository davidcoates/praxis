{-# LANGUAGE OverloadedStrings #-}

module Check.Type.Error
  ( Error(..)
  ) where

import           Common
import           Print
import           Term

data Error = Contradiction (Annotated TypeConstraint)
           | AffineInconsistency (Annotated Type)
           | Underdefined (Annotated TypeConstraint)
           | Stuck

instance Pretty Error where
  pretty = \case
    Contradiction c       -> "found contradiction " <> pretty c
    AffineInconsistency t -> "deduced Affine " <> pretty t <> " and Share " <> pretty t
    Stuck                 -> "infinite loop detected :("
    Underdefined c        -> "failed to completely deduce the unification variable(s) present in " <> pretty c
