module Error
  ( Error(..)
  , ParseSource(..)
  , ParseError(..)
  , CheckError(..)
  ) where

import Check.Derivation (Derivation)
import Source (Source)

data Error = LexicalError ParseSource ParseError
           | SyntaxError  ParseSource ParseError
           | CheckError   CheckError

data ParseSource = Source Source
                 | EOF

data ParseError = Option ParseError ParseError
                | Atom String
                | Generic

data CheckError = Contradiction Derivation
                | Underdefined Derivation
                | NotInScope String

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

instance Show Error where
  show (LexicalError p s) = "Lexical error: " ++ show p ++ " ... " ++ show s
  show (SyntaxError p s)  = "Syntax error: "  ++ show p ++ " ... " ++ show s
  show (CheckError e)     = "Check error: "   ++ show e

instance Show CheckError where
  show (Contradiction d) = show d
  show (Underdefined d)  = "Failed to completely deduce the unification variable(s) present in: " ++ show d
  show (NotInScope s)    = "Not in scope: " ++ s
