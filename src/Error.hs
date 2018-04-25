module Error
  ( Error(..)
  , SyntaxError(..)
  , CheckError(..)
  , ParseSource(..)
  , ParseError(..)
  ) where

import Check.Derivation (Derivation)
import Source (Source)

data Error = LexicalError ParseSource ParseError
           | SyntaxError  SyntaxError
           | CheckError   CheckError

data ParseSource = Source Source
                 | EOF

data ParseError = Option ParseError ParseError
                | Atom String
                | Generic

data SyntaxError = SweetError ParseSource ParseError
                 | InfixError -- TODO

data CheckError = Contradiction Derivation
                | Underdefined Derivation
                | NotInScope String

instance Show Error where
  show (LexicalError s e) = "Lexical error: " ++ show s ++ " ... " ++ show e
  show (SyntaxError e)    = "Syntax error: "  ++ show e
  show (CheckError e)     = "Check error: "   ++ show e

instance Show ParseSource where
  show EOF = "<end of file>"
  show (Source s) = show s

instance Show ParseError where
  show e = case toList e of
    []  -> "<unknown>"
    [x] -> "expected " ++ x
    xs  -> "expected one of " ++ show xs
    where toList (Option a b) = toList a ++ toList b
          toList (Atom s)     = [s]
          toList Generic      = []

instance Show SyntaxError where
  show (SweetError s e) = show s ++ " ... " ++ show e
  show InfixError       = "TODO <infix error>"

instance Show CheckError where
  show (Contradiction d) = show d
  show (Underdefined d)  = "Failed to completely deduce the unification variable(s) present in: " ++ show d
  show (NotInScope s)    = "Not in scope: " ++ s
