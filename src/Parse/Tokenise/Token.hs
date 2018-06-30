{-# LANGUAGE FlexibleInstances #-}

module Parse.Tokenise.Token
  ( Annotated
  , Token(..)
  , Lit(..)
  ) where

import           AST    (Lit (..), QString (..))
import           Pretty
import           Source
import           Tag

type Annotated a = Tag Source a

data Token = QVarId QString
           | QConId QString
           | QVarSym QString
           | QConSym QString
           | ReservedOp String
           | ReservedId String
           | Lit Lit
           | Special Char
           | Whitespace -- ^Consider whitespace a token to allow parser to construct accurate spelling

instance Show Token where
  show (QVarId q)     = show q
  show (QConId q)     = show q
  show (QVarSym q)    = show q
  show (QConSym q)    = show q
  show (ReservedOp s) = s
  show (ReservedId s) = s
  show (Lit l)        = show l
  show (Special c)    = [c]
  show Whitespace     = ""

instance Show (Annotated Token) where
  show (a :< x) = show x ++ " @ " ++ show a
