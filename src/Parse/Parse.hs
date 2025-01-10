{-# LANGUAGE DataKinds #-}

module Parse.Parse
  ( run
  ) where

import           Common
import           Introspect
import qualified Parse.Parse.Parser as Parser (run)
import           Praxis
import           Print
import           Stage
import           Syntax.Parser
import           Term
import           Token


run :: IsTerm a => [Sourced Token] -> Praxis (Annotated Initial a)
run tokens = do
  term <- Parser.run parse tokens
  display Parse "parsed term" term `ifFlag` debug
  return term
