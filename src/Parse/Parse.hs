{-# LANGUAGE ScopedTypeVariables #-}

module Parse.Parse
  ( run
  ) where

import           Common
import           Introspect
import qualified Parse.Parse.Parser as Parser (run)
import           Praxis
import           Print
import           Stage
import           Syntax
import           Term
import           Token

run :: forall a. Term a => [Sourced Token] -> Praxis (Annotated a)
run tokens = save stage $ do
  stage .= Parse
  term <- Parser.run parse tokens
  display term `ifFlag` debug
  return term
