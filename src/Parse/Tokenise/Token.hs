{-# LANGUAGE FlexibleInstances #-}

module Parse.Tokenise.Token
  ( Token
  , Type(..)
  , Literal(..)
  , QString(..)
  ) where

import Source
import Pretty

type Token = Sourced Type

data Type = QVarId QString
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

-- instance Show Token where
-- show x = showSpelling (source x)

instance Show Token where
  show x = show (value x) ++ "\n" ++ indents [showStart (source x) ++ "->" ++ showEnd (source x), showSpelling (source x)] 
