module Check.Error
  ( Error(..)
  ) where

import qualified Check.Kind.Error as Kind
import qualified Check.Type.Error as Type

import           Common

data Error = NotInScope Name Source
           | TypeError Type.Error
           | KindError Kind.Error

instance Show Error where
  show e = case e of
    NotInScope n s -> " ... " ++ "Variable '" ++ n ++ "' is not in scope" ++ " at " ++ show s
    TypeError e -> show e
    KindError e -> show e
