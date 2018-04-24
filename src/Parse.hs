module Parse
  ( parse
  ) where

import Parse.Tokenise (tokenise)
import qualified Parse.Parse as Inner (parse)
import Parse.Desugar (desugar)
import Compiler

parse :: Compiler ()
parse =  tokenise >> Inner.parse >> desugar
