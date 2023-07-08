module Check.Kind.Reason
  ( Reason(..)
  ) where

import           Common

data Reason = TyFunApplication
            | TyOpApplication
            | DataConType Name
            | DataType Name
            | FunType
            | OpType
            | PairType

-- TODO Pretty
instance Show Reason where
  show = \case
    TyFunApplication -> "type function application"
    TyOpApplication  -> "type operator application"
    DataConType n    -> "data constructor '" ++ n ++ "' must return kind Type"
    DataType n       -> "type constructor'" ++ n ++ "' must have kind Type"
    FunType          -> "type function must have kind (Type -> Type)"
    PairType         -> "type pair must have kind (Type, Type)"
