module Check.Type.Reason
  ( Reason(..)
  ) where

import           Common

data Reason = BindCongruence
            | Captured Name
            | CaseCongruence
            | ConPattern Name
            | FuncApplication
            | FuncCongruence Name
            | FuncSignature Name
            | IfCondition
            | IfCongruence
            | SwitchCondition
            | SwitchCongruence
            | Instance Name
            | MultiAlias Name
            | MultiUse Name
            | UserSignature
            | UnsafeView Name
            | Specialisation

-- TODO Pretty
instance Show Reason where
  show = \case
    BindCongruence   -> "Binding must have same type on both sides"
    Captured n       -> "Variable '" ++ n ++ "' captured"
    CaseCongruence   -> "Alternatives of 'case' expression must have the same type"
    ConPattern n     -> "Constructor pattern '" ++ n ++ "'"
    FuncApplication  -> "Function application"
    FuncCongruence n -> "Function '" ++ n ++ "'"
    FuncSignature n  -> "Function signature for '" ++ n ++ "'"
    IfCondition      -> "Type of 'if' condition must be Bool"
    IfCongruence     -> "Branches of 'if' expression must have the same type"
    SwitchCondition  -> "Type of 'switch' condition must be Bool"
    SwitchCongruence -> "Branches of 'switch' expression must have the same type"
    Instance n       -> "Monomorphic usage of '" ++ n ++ "'"
    MultiAlias n     -> "Variable '" ++ n ++ "' is not a unique alias"
    MultiUse n       -> "Variable '" ++ n ++ "' used more than once"
    UserSignature    -> "User-supplied signature"
    UnsafeView n     -> "Variable '" ++ n ++ "' viewed after being used"
    Specialisation   -> "Specialisation"
