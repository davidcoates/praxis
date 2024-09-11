module Parse.Parse
  ( run
  ) where

import           Common
import           Introspect
import qualified Parse.Parse.Parser as Parser (run)
import           Praxis
import           Print
import           Syntax.Parser
import           Term
import           Token

run :: Term a => [Sourced Token] -> Praxis (Annotated a)
run tokens = do
  term <- Parser.run parse tokens
  display "parsed term" term `ifFlag` debug
  return term
