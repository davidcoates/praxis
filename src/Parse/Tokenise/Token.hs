{-# LANGUAGE FlexibleInstances #-}

module Parse.Tokenise.Token
  ( Token(..)
  ) where

import           AST    (Lit (..), QString (..))
import           Common

data Token = QVarId QString
           | QConId QString
           | QVarSym QString
           | QConSym QString
           | ReservedCon String
           | ReservedOp String
           | ReservedId String
           | Lit Lit
           | Special Char
           | Whitespace -- ^Consider whitespace a token to allow parser to construct accurate spelling

instance Show Token where
  show x = case x of
    QVarId q      -> show q
    QConId q      -> show q
    QVarSym q     -> show q
    QConSym q     -> show q
    ReservedCon s -> s
    ReservedOp s  -> s
    ReservedId s  -> s
    Lit l         -> show l
    Special c     -> [c]
    Whitespace    -> ""
