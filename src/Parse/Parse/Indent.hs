module Parse.Parse.Indent
  ( Parser
  , parse
  , laidout
  , indented
  , align
  , block
  , block1
  ) where

import Text.Parsec (Parsec, SourceName, ParseError, runParser, (<?>), (<|>), many, many1, endBy, endBy1)
import Text.Parsec.Prim (getState, putState)
import Control.Monad (guard)
import Pos
import Parse.Parse.Language

type Parser a = Parsec String IndentState a

type IndentState = Int

parse :: Parser a -> SourceName -> String -> Either ParseError a
parse p = runParser p 0

laidout :: Parser a -> Parser a
laidout p = do
  cur <- getState
  pos <- column <$> currentPos
  putState pos
  x <- p
  putState cur
  return x

indentCmp :: (Int -> Int -> Bool) -> Parser ()
indentCmp cmp = do
  col <- column <$> currentPos
  cur <- getState
  guard (col `cmp` cur)

indented :: Parser ()
indented = indentCmp (>) <?> "Block (indented)"

align :: Parser ()
align = indentCmp (==) <?> "Block (same indentation)"

block, block1 :: Parser a -> Parser [a]
block  p = braces (endBy  p semi) <|> laidout (many  (align >> p))
block1 p = braces (endBy1 p semi) <|> laidout (many1 (align >> p))
