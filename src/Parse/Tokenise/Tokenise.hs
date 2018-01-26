module Tokenise
  ( tokenise
  ) where

import Parse.Tokenise.Tokeniser
import Parse.Tokenise.Token
import Source
import Pos
import Data.Digits (unDigits)

import Control.Applicative (Applicative, Alternative, liftA2, (<|>), empty)
import Data.Char

-- import Compile

{-
tokenise :: Compiler String ()
tokenise = do
  cs <- get src
  case runTokeniser token (sourced cs) of
    (Left e) -> throwError e
    (Right ts) -> set tokens ts
-}

tokenise = undefined

parse :: String -> IO ()
parse x = putStrLn $ (\x -> case x of { Left s -> s; Right x -> show x} ) $ runTokeniser token (sourced x)

sourced :: String -> [Sourced Char]
sourced = sourced' Pos { line = 1, column = 1 }
  where sourced' _     [] = []
        sourced' p (c:cs) = let p' = advance c p in make p c : sourced' p' cs
        make p c = Sourced { value = c, source = Source { start = p, end = p, spelling = [c] } }

advance :: Char -> Pos -> Pos
advance '\t' p = p { column = math (column p) }
  where math = (+ 1) . (* 8) . (+ 1) . (`div` 8) . subtract 1
advance '\n' p = Pos { line = line p + 1, column = 1 }
advance _    p = p { column = column p + 1 }

many :: Tokeniser p -> Tokeniser [p]
many p = liftA2 (:) (try p) (many p) <|> pure []

some :: Tokeniser p -> Tokeniser [p]
some p = liftA2 (:) p (many p)


expected :: String -> String
expected s = "Expected: " ++ s

exclude :: Eq p => Tokeniser p -> p -> Tokeniser p
exclude p x = p >>= (\y -> if y == x then empty else pure y)

excludes :: Eq p => Tokeniser p -> [p] -> Tokeniser p
excludes p xs = p >>= (\y -> if y `elem` xs then empty else pure y)

char :: Char -> Tokeniser Char
char c = satisfy (== c)

anyChar :: Tokeniser Char
anyChar = satisfy (const True)

string :: String -> Tokeniser String
string [c] = (:[]) <$> char c
string (c:cs) = liftA2 (:) (char c) (string cs) 

token :: Tokeniser Type
token = (whitespace *> pure Whitespace) <|> lexeme

lexeme :: Tokeniser Type
lexeme = literal <?> "lexeme"-- char 'a' *> pure (ReservedId "na")

literal :: Tokeniser Type
literal = integer <|> char' <|> string' <?> "literal"-- <|> char <|> string <?> "Expected literal"

char' :: Tokeniser Type
char' = try (char '\'') *> (Literal . Char <$> inner) <* (char '\'' <?> expected "terminating '") <?> "char" 
  where inner = anyChar `excludes` ['\\', '\''] -- TODO

string' :: Tokeniser Type
string' = try (char '\"') *> (Literal . String <$> inner) <* char '\"' <?> "string"
  where inner = many (anyChar `excludes` ['\\','\"']) -- TODO

integer :: Tokeniser Type
integer = Literal . Int <$> decimal <?> "integer"

decimal :: Tokeniser Int
decimal = unDigits 10 <$> liftA2 (:) (try digit) (many digit)

digit :: Tokeniser Int
digit = read . (:[]) <$> satisfy isDigit

whitespace :: Tokeniser String
whitespace = try (concat <$> some whitestuff <?> "whitespace")

whitestuff :: Tokeniser String
whitestuff = whitechar -- <:> comment <:> ncomment

whitechar :: Tokeniser String
whitechar = try newline <|> ((:[]) <$> satisfy isSpace)

newline :: Tokeniser String
newline = try (string "\r\n") <|> try (string "\r") <|> try (string "\n") <|> string "\f"

