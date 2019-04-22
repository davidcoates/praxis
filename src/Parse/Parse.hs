module Parse.Parse
  ( parse
  ) where

-- TODO this is a lot of imports for one function...

import           Annotate
import           Common
import           Parse.Parse.Parser
import           Praxis             hiding (run)
import           Syntax
import           Token

import           Prelude            hiding (log)

parse :: Syntactic a => [Sourced Token] -> Praxis (Parsed a)
parse ts = save stage $ do
  stage .= Parse
  p <- run (annotated syntax) ts
  log Debug p
  return p
