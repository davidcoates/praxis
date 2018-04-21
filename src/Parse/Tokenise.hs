module Parse.Tokenise
  ( tokenise
  ) where

import Parse.Tokenise.Tokeniser
import Parse.Tokenise.Token
import Source
import Data.Digits (unDigits)

import Control.Applicative (Applicative, Alternative, liftA2, (<|>), empty)
import Data.Char

import Compile

tokenise :: Compiler String ()
tokenise = do
  cs <- get src
  case runTokeniser token cs of
    (Left e) -> throwError e
    (Right ts) -> set tokens ts

-- parse :: String -> IO ()
-- parse x = putStrLn $ (\x -> case x of { Left s -> s; Right x -> concatMap (("\n" ++) . show) x} ) $ runTokeniser token x

many :: Tokeniser p -> Tokeniser [p]
many p = liftA2 (:) (try p) (many p) <|> pure []

some :: Tokeniser p -> Tokeniser [p]
some p = liftA2 (:) p (many p)


expected :: String -> String
expected s = "Expected: " ++ s

exclude :: Eq p => Tokeniser p -> p -> Tokeniser p
exclude p x = excludes p [x]

excludes :: Eq p => Tokeniser p -> [p] -> Tokeniser p
excludes p xs = p >>= (\y -> if y `elem` xs then empty else pure y)

char :: Char -> Tokeniser Char
char c = satisfy (== c)

anyChar :: Tokeniser Char
anyChar = satisfy (const True)

oneOf :: [Char] -> Tokeniser Char
oneOf cs = satisfy (`elem` cs)

string :: String -> Tokeniser String
string [c] = (:[]) <$> char c
string (c:cs) = liftA2 (:) (char c) (string cs)

token :: Tokeniser Token
token = (whitespace *> pure Whitespace) <|> lexeme

-- The parsers below here all have a 'prefix' which they match without consuming on failure


lexeme :: Tokeniser Token
lexeme = qvarid <|> literal <|> special <?> "lexeme"

qvarid :: Tokeniser Token
qvarid = qualify <$> varid <?> "qvarid" -- TODO: Qualify
  where qualify s = QVarId (QString {qualification = [], name = s})

varid :: Tokeniser String
varid = q <?> "varid"
  where q = p `excludes` ["if","then","else","let","in"]
        p = liftA2 (:) (try small) (many small) -- TODO

small :: Tokeniser Char
small = satisfy isLower <?> "small" 

special :: Tokeniser Token
special = Special <$> oneOf "(),;[]`{}" <?> "special"

literal :: Tokeniser Token
literal = integer <|> char' <|> string' <?> "literal"

char' :: Tokeniser Token
char' = try (char '\'') *> (Literal . Char <$> inner) <* (char '\'' <?> expected "terminating '") <?> "char" 
  where inner = anyChar `excludes` ['\\', '\''] -- TODO

string' :: Tokeniser Token
string' = try (char '\"') *> (Literal . String <$> inner) <* char '\"' <?> "string"
  where inner = many (anyChar `excludes` ['\\','\"']) -- TODO

integer :: Tokeniser Token
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

