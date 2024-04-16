{-# LANGUAGE OverloadedStrings #-}

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
            | Specialisation Name
            | SwitchCondition
            | SwitchCongruence
            | UnsafeRead Name
            | UserSignature

instance Pretty Reason where
  pretty = \case
    BindCongruence   -> "binding must have same type on both sides"
    Captured n       -> "variable " <> quote (pretty n) <> " captured"
    CaseCongruence   -> "alternatives of case expression must have the same type"
    ConPattern n     -> "constructor pattern " <> quote (pretty n)
    FunApplication   -> "function application"
    FunCongruence n  -> "function " <> quote (pretty n)
    FunSignature n   -> "function signature for " <> quote (pretty n)
    IfCondition      -> "type of if condition must be Bool"
    IfCongruence     -> "branches of if expression must have the same type"
    Instance n       -> "monomorphic usage of " <> quote (pretty n)
    MultiAlias n     -> "variable " <> quote (pretty n) <> " is not a unique alias"
    MultiUse n       -> "variable " <> quote (pretty n) <> " used more than once"
    SafeRead         -> "safe read"
    Specialisation n -> "specialisation of " <> quote (pretty n)
    SwitchCondition  -> "type of switch condition must be Bool"
    SwitchCongruence -> "branches of switch expression must have the same type"
    UnsafeRead n     -> "variable " <> quote (pretty n) <> " read after being used"
    UserSignature    -> "user-supplied signature"
