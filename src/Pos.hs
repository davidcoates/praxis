module Pos
  ( Pos(..)
  , initialPos
  , currentPos
  , errorPos
  ) where

import Text.Parsec (ParsecT)
import Text.Parsec.Pos (SourcePos, sourceLine, sourceColumn)
import qualified Text.Parsec.Error as Parsec (errorPos)
import Text.ParserCombinators.Parsec.Prim (getPosition)

data Pos = Pos { line :: Int, column :: Int }

instance Show Pos where
  show p = show (line p) ++ ":" ++ show (column p)

cast :: SourcePos -> Pos
cast p = Pos { line = sourceLine p, column = sourceColumn p }

initialPos = Pos { line = 1, column = 1 }

currentPos :: Monad m => ParsecT s u m Pos
currentPos = cast <$> getPosition

errorPos = cast <$> Parsec.errorPos
