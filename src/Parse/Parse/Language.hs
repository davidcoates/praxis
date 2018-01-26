module Parse.Parse.Language where

import qualified Text.ParserCombinators.Parsec.Token as Token
import Text.ParserCombinators.Parsec.Language (haskellStyle)

praxisDef =
  haskellStyle
    { Token.reservedNames   = ["let", "in", "if", "then", "else", "True", "False"] -- TODO: Eventually treat True False just like any other data constructor
    , Token.reservedOpNames = ["!", "=", "\\", "->", "=>", "@", "::"]
    }

lexer = Token.makeTokenParser praxisDef

lexeme     = Token.lexeme     lexer
whiteSpace = Token.whiteSpace lexer
operator   = Token.operator   lexer
symbol     = Token.symbol     lexer
parens     = Token.parens     lexer
integer    = Token.integer    lexer
natural    = Token.natural    lexer
reserved   = Token.reserved   lexer
reservedOp = Token.reservedOp lexer
identifier = Token.identifier lexer
semi       = Token.semi       lexer
braces     = Token.braces     lexer
