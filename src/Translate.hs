module Translate
  ( runProgram
  , Mode(..)
  ) where

import           Common
import           Praxis
import           Stage
import           Term


data Mode = NoPrelude | Prelude | PreludeWithMain

runProgram :: Mode -> Annotated Program -> Praxis String
runProgram mode program = save stage $ do
  stage .= Translate
  program <- translateProgram program
  display program `ifFlag` debug
  return program
{-
  let wrappedProgram = prelude ++ "namespace praxis::user {\n" ++ program ++ "\n}"
  case mode of
    NoPrelude       -> return program
    Prelude         -> return wrappedProgram
    PreludeWithMain -> requireMain >> return (wrappedProgram ++ "\nint main(){ praxis::user::main_0(std::monostate{}); }")
-}


translateProgram :: Annotated Program -> Praxis String
translateProgram (_ :< Program decls) = return "TODO"
