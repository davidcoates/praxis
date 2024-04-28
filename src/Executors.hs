module Executors
  ( translateProgram
  , evaluateProgram
  , evaluateExp
  ) where

import           Check     (check)
import           Common
import           Parse     (parse)
import           Praxis
import           Term
import qualified Translate

translateProgram :: String -> Praxis String
translateProgram = translateProgram' Translate.NoPrelude

translateProgram' :: Translate.Mode -> String -> Praxis String
translateProgram' mode program = do
  program <- parse program >>= check :: Praxis (Annotated Program)
  translation <- Translate.runProgram mode program
  return translation

evaluateProgram :: String -> Praxis String
evaluateProgram program = return "TODO"

evaluateExp :: String -> Praxis String
evaluateExp exp = return "TODO"
