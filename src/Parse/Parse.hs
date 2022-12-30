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
run ts = save stage $ do
  stage .= Parse
  p <- Parser.run parse ts
  display p `ifFlag` debug
  return p
