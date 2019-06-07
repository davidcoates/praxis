{-# LANGUAGE OverloadedStrings #-}

module Check.Error
  ( Error(..)
  ) where

import           Common

data Error = NotInScope Name

instance Pretty Error where
  pretty (NotInScope n) = "variable " <> quote (plain n) <> " is not in scope"
