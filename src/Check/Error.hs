{-# LANGUAGE OverloadedStrings #-}

module Check.Error
  ( Error(..)
  ) where

import           Common

data Error = NotInScope Name | Unused Name

instance Pretty Error where
  pretty = \case
    NotInScope n    -> quote (pretty n) <> " is not in scope"
    Unused n        -> quote (pretty n) <> " is not used"
