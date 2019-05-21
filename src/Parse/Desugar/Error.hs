{-# LANGUAGE OverloadedStrings #-}

module Parse.Desugar.Error
  ( Error(..)
  ) where

import           Common

data Error = BangError Name Source
           | LacksBinding Name Source
           | DoError Source
           | RecordError Source
           | InfixError

instance Pretty Error where
  pretty e = case e of
    BangError n s    -> "Observed variable '" <> plain n <> "' is not the argument of a function" <> " at " <> pretty s
    LacksBinding n s -> "Variable '" <> plain n <> "' lacks a binding" <> " at " <> pretty s
    DoError s        -> "Last statement of a 'do' block is not an expression" <> " at " <> pretty s
    RecordError s    -> "Illegal one-field record" <> " at " <> pretty s
    InfixError       -> "TODO <infix error>"


