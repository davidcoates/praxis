{-# LANGUAGE FlexibleInstances #-}

module Parse.Tokenise.Token
  ( Annotated
  , Token(..)
  , Lit(..)
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
           | Lit Lit
           | Special Char
           | Whitespace -- ^Consider whitespace a token to allow parser to construct accurate spelling
  deriving (Show)

data Lit = Int Int | Float Float | Char Char | String String
  deriving (Show)

data QString = QString { qualification :: [String], name :: String }
  deriving (Show)

instance Show (Annotated Token) where
  show (a :< x) = show x ++ " @ " ++ show a
