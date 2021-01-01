module Check.Type.Reason
  ( Reason(..)
  ) where

import           Common

data Reason = AppFun
            | BindCongruence
            | Captured Name
            | CaseCongruence
            | ConPattern Name
            | IfCondition
            | IfCongruence
            | Instance Name
            | Shared Name
            | UnsafeView Name
            | UserSignature (Maybe Name)

-- TODO Pretty
instance Show Reason where
  show = \case
    AppFun           -> "Function application"
    BindCongruence   -> "Binding must have same type on both sides"
    Captured n       -> "Variable '" ++ n ++ "' captured"
    CaseCongruence   -> "Alternatives of <case> expression must have the same type"
    ConPattern n     -> "Constructor pattern '" ++ n ++ "'"
    IfCondition      -> "Type of <if> condition must be Bool"
    IfCongruence     -> "Branches of <if> expression must have the same type"
    Instance n       -> "Monomorphic usage of '" ++ n ++ "'"
    Shared n         -> "Variable '" ++ n ++ "' used more than once"
    UserSignature n  | Just f <- n -> "User-supplied signature '" ++ f ++ "'"
                     | otherwise   -> "User-supplied signature"
    UnsafeView n     -> "Variable '" ++ n ++ "' viewed after being used"
