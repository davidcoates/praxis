{-# LANGUAGE OverloadedStrings #-}

module Check.Error
  ( Error(..)
  ) where

import           Common

data Error = NotInScope Name Source

instance Pretty Error where
  pretty (NotInScope n s) = "variable '" <> plain n <> "' not in scope at " <> pretty s
