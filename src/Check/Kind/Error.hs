{-# LANGUAGE OverloadedStrings #-}

module Check.Kind.Error
  ( Error(..)
  ) where

import           Annotate
import           Common
import           Kind

data Error = Contradiction (Kinded Constraint)
           | Stuck

instance Pretty Error where
  pretty e = case e of
    Contradiction c -> "found contradiction " <> pretty c
    Stuck           -> "infinite loop detected :("
