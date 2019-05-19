{-# LANGUAGE ScopedTypeVariables #-}

module Parse.Parse
  ( parse
  ) where

-- TODO this is a lot of imports for one function...

import           Annotate
import           Common
import           Introspect
import           Parse.Parse.Parser
import           Praxis             hiding (run)
import qualified Syntax             (parse)
import           Token

import           Prelude            hiding (log)

parse :: forall a. Recursive a => [Sourced Token] -> Praxis (Parsed a)
parse ts = save stage $ do
  stage .= Parse
  p <- run Syntax.parse ts
  log Debug p
  return p
