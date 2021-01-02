module Parse.Tokenise
  ( run
  ) where

import           Common                   hiding (asum)
import qualified Parse.Tokenise.Layout    as Layout
import           Parse.Tokenise.Tokeniser hiding (run)
import qualified Parse.Tokenise.Tokeniser as Tokeniser (run)
import           Praxis                   hiding (throw)
import qualified Stage
import           Term                     (Lit (..))
import           Token

import           Control.Applicative      (Alternative (..), Applicative (..))
import           Data.Foldable            (asum)
import           Data.List                (intercalate)
import           Prelude                  hiding (until)

run :: Bool -> String -> Praxis [Sourced Token]
run top s = save stage $ do
  stage .= Stage.Tokenise
  ts <- Tokeniser.run token s
  display (separate " " (map (view value) ts)) `ifFlag` debug
  stage .= Stage.Layout
  let ts' = Layout.layout top ts
  display (separate " " (map (view value) ts')) `ifFlag` debug
  return ts'

-- Helper functions
until :: Tokeniser a -> Tokeniser b -> Tokeniser [b]
until p t = (p *> pure []) <|> ((:) <$> t <*> until p t)

while :: Tokeniser a -> Tokeniser b -> Tokeniser [b]
while p t = (p *> ((:) <$> t <*> while p t)) <|> pure []

char :: Char -> Tokeniser Char
char c = match (== c)

isSymbol = (`elem` "!#$%&*+./<=>?@\\^|-~:[]")
isLower = (`elem` ['a'..'z'])
isUpper = (`elem` ['A'..'Z'])
isDigit = (`elem` ['0'..'9'])
isSpace = (`elem` " \t")
isAlphaNum c = isLower c || isUpper c || isDigit c
isLetter c = c `elem` "_\'" || isAlphaNum c

token :: Tokeniser (Maybe Token)
token = (whitespace *> pure Nothing) <|> (Just <$> (layout <|> special <|> literal <|> tyOpVar <|> stuff)) <|> throw "illegal character"

whitespace :: Tokeniser ()
whitespace = newline <|> space <|> comment
  where newline = match (`elem` "\r\n\f") *> pure ()
        space = match isSpace *> pure ()
        comment = matches 2 (== "--") *> until newline consume *> pure ()

layout :: Tokeniser Token
layout = Layout <$> match (`elem` "{};")

special :: Tokeniser Token
special = Special <$> match (`elem` "(),`_")

literal :: Tokeniser Token
literal = int <|> chara <|> string

int :: Tokeniser Token
int = satisfy isDigit *> (Lit . Int <$> decimal)
  where decimal :: Tokeniser Int
        decimal = read <$> while (satisfy isDigit) consume

tyOpVar :: Tokeniser Token
tyOpVar = char '?' *> (TyOpVar <$> (satisfy isLower *> while (satisfy isLetter) consume))

-- TODO
escape :: Char -> Char
escape 'n' = '\n'
escape x   = x

chara :: Tokeniser Token
chara = char '\'' *> ((Lit . Char <$> inner) <* char '\'' <|> throw "unterminated character literal") where
  inner :: Tokeniser Char
  inner = (char '\\' *> (escape <$> consume)) <|> match (/= '\'')

string :: Tokeniser Token
string = char '"' *> ((Lit . String <$> inner) <* char '"' <|> throw "unterminated string literal") where
  inner :: Tokeniser String
  inner = while (satisfy (/= '"')) ((char '\\' *> (escape <$> consume)) <|> consume)

reservedIds = ["read", "in", "if", "then", "else", "using", "type", "interface", "instance", "cases", "case", "of", "where", "do", "forall", "let", "operator"]
reservedCons = ["Type", "Constraint", "Share"]
reservedOps = [":", "=>", "=", "\\", "->", "@", "&", "<id>", "?"]

-- Possibly qualified, possibly reserved conid / varid / consym / varsym
stuff :: Tokeniser Token
stuff = form <$> stuff' where
  stuff' = ((:[]) <$> varid) <|> ((:[]) <$> sym) <|> qualified
  varid = satisfy isLower *> while (satisfy isLetter) consume
  conid = satisfy isUpper *> while (satisfy isLetter) consume
  sym = satisfy isSymbol *> while (satisfy isSymbol) consume
  qualified = (:) <$> conid <*> ((satisfies 2 (\[x, y] -> x == '.' && (isLower y || isUpper y || isSymbol y)) *> consume *> stuff') <|> pure [])
  form :: [String] -> Token
  form [x] | x `elem` reservedIds = ReservedId x
           | x `elem` reservedCons = ReservedCon x
           | x `elem` reservedOps = ReservedOp x
  form xs = let qs = Qualified { qualification = init xs, unqualify = last xs } in case last xs of
    x | isLower (head x) -> QVarId qs
    x | isUpper (head x) -> QConId qs
    x | head x == ':'    -> QConSym qs
    _                    -> QVarSym qs
