module Check.Type.Reason
  ( Reason(..)
  ) where

import           Common

data Reason = BindCongruence
            | Captured Name
            | CaseCongruence
            | ConPattern Name
            | FunApplication
            | FunCongruence Name
            | FunSignature Name
            | IfCondition
            | IfCongruence
            | Instance Name
            | MultiAlias Name
            | MultiUse Name
            | SafeRead
            | Specialisation
            | SwitchCondition
            | SwitchCongruence
            | UnsafeView Name
            | UserSignature

-- TODO Pretty
instance Show Reason where
  show = \case
    BindCongruence   -> "binding must have same type on both sides"
    Captured n       -> "variable '" ++ n ++ "' captured"
    CaseCongruence   -> "alternatives of 'case' expression must have the same type"
    ConPattern n     -> "constructor pattern '" ++ n ++ "'"
    FunApplication   -> "function application"
    FunCongruence n  -> "function '" ++ n ++ "'"
    FunSignature n   -> "function signature for '" ++ n ++ "'"
    IfCondition      -> "type of 'if' condition must be Bool"
    IfCongruence     -> "branches of 'if' expression must have the same type"
    Instance n       -> "monomorphic usage of '" ++ n ++ "'"
    MultiAlias n     -> "variable '" ++ n ++ "' is not a unique alias"
    MultiUse n       -> "variable '" ++ n ++ "' used more than once"
    SafeRead         -> "safe read"
    Specialisation   -> "specialisation"
    SwitchCondition  -> "type of 'switch' condition must be Bool"
    SwitchCongruence -> "branches of 'switch' expression must have the same type"
    UnsafeView n     -> "variable '" ++ n ++ "' viewed after being used"
    UserSignature    -> "user-supplied signature"
