module Parse.Desugar.Error
  ( DesugarError(..)
  , InfixError(..)
  ) where

import Parse.Desugar.Infix
import Parse.Parse.AST (Op)
import Pretty (indent)

data DesugarError = InfixError InfixError

instance Show DesugarError where
  show (InfixError e) = "precedence error when trying to structure infix expression\n" ++ indent (show e)

data InfixError = BadNeg (Op, Fixity) | BadPrec (Op, Fixity) (Op, Fixity)

instance Show InfixError where
  show (BadNeg (o, f))             = "cannot mix '" ++ o  ++ "' " ++ show f  ++ " and prefix '-' [infixl 6] in the same infix expression"
  show (BadPrec (o1, f1) (o2, f2)) = "cannot mix '" ++ o1 ++ "' " ++ show f1 ++ " and '" ++ o2 ++ "' " ++ show f2 ++ " in the same infix expression"
