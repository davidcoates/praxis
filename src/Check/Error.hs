{-# LANGUAGE OverloadedStrings #-}

module Check.Error
  ( Error(..)
  ) where

import           Common
import           Pretty

data Error = NotInScope Name

instance Pretty Error where
  pretty (NotInScope n) = "variable " <> quote (pretty n) <> " is not in scope"
