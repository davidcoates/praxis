{-# LANGUAGE ScopedTypeVariables #-}

module Parse.Parse
  ( run
  ) where

-- TODO this is a lot of imports for one function...

import           Common
import           Introspect
import qualified Parse.Parse.Parser as Parser (run)
import           Praxis
import           Print
import           Stage
import           Syntax
import           Term
import           Token

run :: forall a. Recursive a => [Sourced Token] -> Praxis (Simple a)
run ts = save stage $ do
  stage .= Parse
  p <- Parser.run parse ts
  output p
  return p
