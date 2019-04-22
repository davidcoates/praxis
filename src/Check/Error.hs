module Check.Error
  ( Error(..)
  ) where

import           Common

data Error = NotInScope Name Source

instance Show Error where
  show (NotInScope n s) = "variable '" ++ n ++ "' not in scope at " ++ show s
