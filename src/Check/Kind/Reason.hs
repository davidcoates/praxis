module Check.Kind.Reason
  ( Reason(..)
  ) where

import           Common

data Reason = AppType Name
            | DataAltType Name
            | DataType Name
            | FunType
            | OpType
            | PairType

-- TODO Pretty
instance Show Reason where
  show = \case
    AppType n     -> "Application of constructor '" ++ n ++ "'"
    DataAltType n -> "Data type constructor '" ++ n ++ "' must return a Type"
    DataType n    -> "Data type '" ++ n ++ "' must be a Type"
    FunType       -> "Function type"
    OpType        -> "Type operator"
    PairType      -> "Type pair"
