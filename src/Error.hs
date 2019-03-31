module Error
  ( Error(..)
  , SyntaxError(..)
  , ParseSource(..)
  , ParseError(..)
  ) where

import qualified Check.Error as Check
import           Common
import           Stage

-- TODO move errors to subdirs like Check.Error
data Error = LexicalError ParseSource ParseError
           | SyntaxError  SyntaxError
           | CheckError Check.Error

data ParseSource = Source Source
                 | EOF

data ParseError = Option ParseError ParseError
                | Atom String
                | Generic

data SyntaxError = SweetError ParseSource ParseError
                 | BangError Source Name
                 | LacksBinding Name Source
                 | DoError Source
                 | InfixError -- TODO

instance Show Error where
  show e = case e of
    LexicalError s e -> "Lexical error: " ++ show e ++ " at " ++ show s
    SyntaxError e    -> "Syntax error: " -- ++ show e
    CheckError e     -> "Check error: " -- ++ show e

instance Show ParseSource where
  show EOF              = "<end of file>"
  show (Error.Source s) = show s

instance Show ParseError where
  show e = case toList e of
    []  -> "<unknown>"
    [x] -> "expected " ++ x
    xs  -> "expected one of " ++ show xs
    where toList (Option a b) = toList a ++ toList b
          toList (Atom s)     = [s]
          toList Generic      = []

{-
instance Show SyntaxError where
  show e = case e of
    SweetError s e -> show s ++ " ... " ++ show e
    BangError s n  -> show s ++ " ... " ++ "Observed variable '" ++ show n ++ "' is not the argument of a function"
    DeclError e    -> show e
    DoError s      -> show s ++ " ... " ++ "Last statement of a 'do' block is not an expression"
    InfixError     -> "TODO <infix error>"

instance Show DeclError where
  show (MismatchedArity n (s1,i1) (s2,i2)) = "Mismatched arities for function '" ++ n ++ "'. Declared with arities " ++ show i1 ++ " at " ++ show s1 ++ " and " ++ show i2 ++ " at " ++ show s2
  show (LacksBinding n s) = "The function '" ++ n ++ "' at " ++ show s ++ " lacks an accompanying binding"

instance Show CheckError where
  show e = case e of
    Contradiction d -> "Contradiction: " ++ show d
    NotInScope n s  -> "Not in scope: " ++ n ++ " at " ++ show s
    Stuck           -> "Infinite loop detected :("
    Underdefined d  -> "Failed to completely deduce the unification variable(s) present in: " ++ show d
-}
