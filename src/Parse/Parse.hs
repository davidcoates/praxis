{-# LANGUAGE ScopedTypeVariables #-}

module Parse.Parse
  ( run
  ) where

-- TODO this is a lot of imports for one function...

import           Annotate
import           Common
import           Introspect
import qualified Parse.Parse.Parser as Parser (run)
import           Praxis
import           Syntax
import           Token

run :: forall a. Recursive a => [Sourced Token] -> Praxis (Parsed a)
run ts = save stage $ do
  stage .= Parse
  p <- Parser.run parse ts
  output p
  return p
