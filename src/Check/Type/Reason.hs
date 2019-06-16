module Check.Type.Reason
  ( Reason(..)
  ) where

import           Common

data Reason = AppFun
            | Captured Name
            | CaseCongruence
            | Custom String
            | IfCondition
            | IfCongruence
            | Instance Name
            | Shared Name
            | Unknown
            | UnsafeView Name
            | UserSignature (Maybe Name)

instance Show Reason where
  show = \case
    AppFun           -> "Function application"
    Captured n       -> "Variable '" ++ n ++ "' captured"
    CaseCongruence   -> "Alternatives of <case> expression must have the same type"
    Custom s         -> s
    IfCondition      -> "Type of <if> condition must be Bool"
    IfCongruence     -> "Branches of <if> expression must have the same type"
    Instance n       -> "Monomorphic usage of '" ++ n ++ "'"
    Shared n         -> "Variable '" ++ n ++ "' used more than once"
    Unknown          -> "<Unknown>"
    UserSignature n  | Just f <- n -> "User-supplied signature '" ++ f ++ "'"
                     | otherwise   -> "User-supplied signature"
    UnsafeView n     -> "Variable '" ++ n ++ "' used before being viewed"
