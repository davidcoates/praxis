module Parse
  ( parse
  ) where

import Parse.Tokenise (tokenise)
import qualified Parse.Parse as Inner (parse)
import Parse.Desugar (desugar)
import Compile

parse :: Compiler String ()
parse =  tokenise >> Innter.parse >> desugar
