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
data Error = LexicalError ParseError ParseSource
           | SyntaxError  SyntaxError
           | CheckError Check.Error

-- TODO should EOF be an option in Source?
data ParseSource = Source Source
                 | EOF

data ParseError = Option ParseError ParseError
                | Atom String
                | Generic

data SyntaxError = SweetError ParseError ParseSource
                 | BangError Name Source
                 | LacksBinding Name Source
                 | DoError Source
                 | InfixError -- TODO

instance Show Error where
  show e = case e of
    LexicalError e s -> show e ++ " at " ++ show s
    SyntaxError e    -> show e
    CheckError e     -> show e

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

instance Show SyntaxError where
  show e = case e of
    SweetError e s-> show e ++ " at " ++ show s
    BangError n s  -> "Observed variable '" ++ n ++ "' is not the argument of a function" ++ " at " ++ show s
    LacksBinding n s -> "Variable '" ++ n ++ "' lacks a binding" ++ " at " ++ show s
    DoError s      -> "Last statement of a 'do' block is not an expression" ++ " at " ++ show s
    InfixError     -> "TODO <infix error>"
