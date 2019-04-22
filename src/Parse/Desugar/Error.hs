module Parse.Desugar.Error
  ( Error(..)
  ) where

import           Common

data Error = BangError Name Source
           | LacksBinding Name Source
           | DoError Source
           | RecordError Source
           | InfixError

instance Show Error where
  show e = case e of
    BangError n s    -> "Observed variable '" ++ n ++ "' is not the argument of a function" ++ " at " ++ show s
    LacksBinding n s -> "Variable '" ++ n ++ "' lacks a binding" ++ " at " ++ show s
    DoError s        -> "Last statement of a 'do' block is not an expression" ++ " at " ++ show s
    RecordError s    -> "Illegal one-field record" ++ " at " ++ show s
    InfixError       -> "TODO <infix error>"


