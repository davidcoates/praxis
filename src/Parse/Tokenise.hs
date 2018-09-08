module Parse.Tokenise
  ( tokenise
  ) where

import           AST                      (Lit (..), QString (..))
import           Parse.Tokenise.Layout
import           Parse.Tokenise.Token
import           Parse.Tokenise.Tokeniser
import           Praxis                   hiding (try)
import           Source
import           Tag

import           Control.Applicative      (Alternative, Applicative, empty,
                                           liftA2, (<|>))
import           Data.Char
import           Data.Foldable            (asum)
import           Data.List                (intercalate)

tokenise :: Bool -> String -> Praxis [Annotated Token]
tokenise topLevel s = save stage $ do
  set stage Tokenise
  ts <- runTokeniser atom s
  let ts' = layout topLevel ts
  logStr Debug (showTokens ts')
  return ts'
    where showTokens = unwords . map (show . value) . filter (\x -> case value x of { Whitespace -> False ; _ -> True })

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
string [c]    = (:[]) <$> char c
string (c:cs) = liftA2 (:) (char c) (string cs)

atom :: Tokeniser Token
atom = (whitespace *> pure Whitespace) <|> lexeme

-- // END OF NON-BACKTRACKING PARSER COMBINATORS


reservedids = ["read", "in", "if", "then", "else", "using", "data", "class", "instance", "cases", "case", "of", "where", "do", "forall"]
reservedops = [":", "=>", "=", "\\", "->", "#", "@", "|"]

lexeme :: Tokeniser Token
lexeme = qstuff <|> reservedid <|> reservedop <|> literal <|> special <|?> "lexeme"

modid :: Tokeniser [String]
modid = liftA2 (:) conid (many (try (char '.' *> conid)))

conid :: Tokeniser String
conid = liftA2 (:) (try large) (many idLetter) <?> "conid"

varid :: Tokeniser String
varid = liftA2 (:) (try small) (many idLetter) `excludes` reservedids <?> "varid"

idLetter :: Tokeniser Char
idLetter = try (satisfy isAlphaNum) <|> try (char '_') <|> try (char '\'')

varsym :: Tokeniser String
varsym = try (liftA2 (:) (symbol `exclude` ':') (many symbol) `excludes` reservedops) <?> "varsym" -- TODO exclude dashes

consym :: Tokeniser String
consym = try (liftA2 (:) (char ':') (many symbol) `excludes` reservedops) <?> "consym"

qstuff :: Tokeniser Token
qstuff = try $ do
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
special = Special <$> try (oneOf "(),;[]`{}_") <?> "special"  -- TODO should _ be special?

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

whitestuff :: Tokeniser String
whitestuff = whitechar <|> comment

comment :: Tokeniser String
comment = try (string "--") *> many (satisfy (\x -> not (x `elem` "\r\n\f"))) *> newline

whitechar :: Tokeniser String
whitechar = try newline <|> try ((:[]) <$> satisfy isSpace)

newline :: Tokeniser String
newline = try (string "\r\n") <|> try (string "\r") <|> try (string "\n") <|> string "\f"

