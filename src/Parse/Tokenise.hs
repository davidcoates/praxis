module Parse.Tokenise
  ( tokenise
  ) where

import Parse.Tokenise.Tokeniser
import Parse.Tokenise.Token
import Source
import Data.Digits (unDigits)

import Control.Applicative (Applicative, Alternative, liftA2, (<|>), empty)
import Data.Foldable (asum)
import Data.Char

import Compiler

tokenise :: Compiler ()
tokenise = do
  set stage Tokenise
  cs <- get src
  case runTokeniser atom cs of
    Left e   -> throwError e
    Right ts -> set tokens ts >> debugPrint ts


-- // START OF NON-BACKTRACKING PARSER COMBINATORS

many :: Tokeniser p -> Tokeniser [p]
many p = liftA2 (:) (try p) (many p) <|> pure []

some :: Tokeniser p -> Tokeniser [p]
some p = liftA2 (:) p (many p)

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

atom :: Tokeniser Token
atom = (whitespace *> pure Whitespace) <|> lexeme

whitestuff :: Tokeniser String
whitestuff = whitechar -- TODO <:> comment <:> ncomment

-- // END OF NON-BACKTRACKING PARSER COMBINATORS


reservedids = ["let", "in", "if", "then", "else"]
reservedops = [":", "=", "\\", "->", "@", "=>", "|"]

lexeme :: Tokeniser Token
lexeme = qstuff <|> reservedid <|> reservedop <|> literal <|> special <|?> "lexeme"

modid :: Tokeniser [String]
modid = liftA2 (:) conid (many (try (char '.' *> conid)))

conid :: Tokeniser String
conid = try (liftA2 (:) large (many small)) <?> "conid"

varid :: Tokeniser String
varid = try (some small `excludes` reservedids) <?> "varid"

varsym :: Tokeniser String
varsym = try (liftA2 (:) (symbol `exclude` ':') (many symbol) `excludes` reservedops) <?> "varsym" -- TODO exclude dashes

consym :: Tokeniser String
consym = try (liftA2 (:) (char ':') (many symbol) `excludes` reservedops) <?> "consym"

qstuff :: Tokeniser Token
qstuff = do
  qs <- modid <|> pure []
  let simple = fmap (\(f, s) -> f QString{qualification=[], name=s}) stuff
  let full   = fmap (\(f, s) -> f QString{qualification=qs, name=s}) (try (char '.' *> stuff)) <|> pure (QConId QString{qualification = init qs, name = last qs})
  if null qs then simple else full
    where stuff :: Tokeniser (QString -> Token, String)
          stuff = qualify QVarId varid <|> qualify QConId conid <|> qualify QVarSym varsym <|> qualify QConSym consym <|?> "varid, conid, varsym, or consym"
          qualify f = fmap (\s -> (f, s))

reservedid :: Tokeniser Token
reservedid = ReservedId <$> asum (map (try . string) reservedids)

reservedop :: Tokeniser Token
reservedop = ReservedOp <$> asum (map (try . string) reservedops)

small :: Tokeniser Char
small = try (satisfy isLower) <?> "small"

large :: Tokeniser Char
large = try (satisfy isUpper) <?> "large"

symbol :: Tokeniser Char
symbol = ascSymbol <|> try (satisfy isSymbol) <?> "symbol"

ascSymbol :: Tokeniser Char 
ascSymbol = try $ oneOf "!#$%&*+./<=>?@\\^|-~:"

special :: Tokeniser Token
special = Special <$> try (oneOf "(),;[]`{}") <?> "special"

literal :: Tokeniser Token
literal = integer <|> charLit <|> stringLit <|?> "literal"

charLit :: Tokeniser Token
charLit = try (char '\'') *> (Lit . Char <$> inner) <* (char '\'' <?> "terminating '") <?> "char"
  where inner = anyChar `excludes` ['\\', '\''] -- TODO

stringLit :: Tokeniser Token
stringLit = try (char '\"') *> (Lit . String <$> inner) <* char '\"' <?> "string"
  where inner = many (anyChar `excludes` ['\\','\"']) -- TODO

integer :: Tokeniser Token
integer = Lit . Int <$> decimal <?> "integer"
  where decimal :: Tokeniser Int
        decimal = read <$> some (try (satisfy isDigit))

whitespace :: Tokeniser String
whitespace = try (concat <$> some whitestuff) <?> "whitespace"

whitechar :: Tokeniser String
whitechar = try newline <|> ((:[]) <$> satisfy isSpace)

newline :: Tokeniser String
newline = try (string "\r\n") <|> try (string "\r") <|> try (string "\n") <|> string "\f"

