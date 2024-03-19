module Translate
  ( runProgram
  ) where

import           Common
import           Praxis
import           Stage
import           Term

runProgram :: Annotated Program -> Praxis String
runProgram program = save stage $ do
  stage .= Translate
  translateProgram program

translateProgram :: Annotated Program -> Praxis String
translateProgram program = return "TODO"
