module Error
  ( Error(..)
  , SyntaxError(..)
  , CheckError(..)
  , DeclError(..)
  , ParseSource(..)
  , ParseError(..)
  ) where

import Check.Derivation (Derivation)
import Source (Source)
import Common

data Error = LexicalError ParseSource ParseError
           | SyntaxError  SyntaxError
           | CheckError   CheckError

data ParseSource = Source Source
                 | EOF

data ParseError = Option ParseError ParseError
                | Atom String
                | Generic

data SyntaxError = SweetError ParseSource ParseError
                 | DeclError DeclError
                 | InfixError -- TODO

data DeclError = MismatchedArity Name (Source, Int) (Source, Int)
               | LacksBinding Name Source

data CheckError = Contradiction Derivation
                | Underdefined Derivation
                | NotInScope String

instance Show Error where
  show (LexicalError s e) = "Lexical error: " ++ show e ++ " at " ++ show s
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
  show (DeclError e)    = show e
  show InfixError       = "TODO <infix error>"

instance Show DeclError where
  show (MismatchedArity n (s1,i1) (s2,i2)) = "Mismatched arities for function '" ++ n ++ "'. Declared with arities " ++ show i1 ++ " at " ++ show s1 ++ " and " ++ show i2 ++ " at " ++ show s2
  show (LacksBinding n s) = "The function '" ++ n ++ "' at " ++ show s ++ " lacks an accompanying binding" 

instance Show CheckError where
  show (Contradiction d) = show d
  show (Underdefined d)  = "Failed to completely deduce the unification variable(s) present in: " ++ show d
  show (NotInScope s)    = "Not in scope: " ++ s
