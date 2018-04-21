{-# LANGUAGE FlexibleInstances #-}

module Parse.Tokenise.Token
  ( Annotated
  , Token(..)
  , Literal(..)
  , QString(..)
  ) where

import Source
import Tag
import Pretty

type Annotated a = Tag Source a

data Token = QVarId QString
           | QConId QString
           | QVarSym QString
           | QConSym QString
           | ReservedOp String
           | ReservedId String
           | Literal Literal
           | Special Char
           | Whitespace -- ^ Consider whitespace a token to allow parser to construct accurate spelling
  deriving (Show)

data Literal = Int Int | Float Float | Char Char | String String
  deriving (Show)

data QString = QString { qualification :: [String], name :: String }
  deriving (Show)

instance Show (Annotated Token) where
  show (a :< x) = show x ++ "\n" ++ indents [showStart a ++ "->" ++ showEnd a, showSpelling a]
