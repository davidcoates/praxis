{-# LANGUAGE OverloadedStrings #-}

module Check.Kind.Reason
  ( Reason(..)
  ) where

import           Common


data Reason = TyFunApplication
            | ViewApplication
            | DataConType Name
            | DataType Name
            | FunType
            | OpType
            | PairType

instance Pretty Reason where
  pretty = \case
    TyFunApplication -> "type function application"
    ViewApplication  -> "view application"
    DataConType n    -> "data constructor " <> quote (pretty n) <> " must return kind Type"
    DataType n       -> "type constructor " <> quote (pretty n) <> " must have kind Type"
    FunType          -> "type function must have kind (Type -> Type)"
    PairType         -> "type pair must have kind (Type, Type)"
