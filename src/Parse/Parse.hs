{-# LANGUAGE DataKinds #-}

module Parse.Parse
  ( run
  ) where

import           Common
import           Introspect
import           Parse.Parse.Parser (parse)
import           Praxis
import           Print
import           Stage
import           Term
import           Token


run :: IsTerm a => [Sourced Token] -> Praxis (Annotated Initial a)
run tokens = do
  term <- parse tokens
  display Parse "parsed term" term `ifFlag` debug
  return term
