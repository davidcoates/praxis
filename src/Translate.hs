module Translate
  ( translate
  , Mode(..)
  ) where

import           Common
import           Introspect
import           Praxis
import           Stage
import           Term
import qualified Translate.Translate as Translate


data Mode = NoPrelude | Prelude | PreludeWithMain

translate :: Mode -> Annotated Program -> Praxis String
translate mode program = save stage $ do
  stage .= Translate
  Translate.run program

{-
  let wrappedProgram = prelude ++ "namespace praxis::user {\n" ++ program ++ "\n}"
  case mode of
    NoPrelude       -> return program
    Prelude         -> return wrappedProgram
    PreludeWithMain -> requireMain >> return (wrappedProgram ++ "\nint main(){ praxis::user::main_0(std::monostate{}); }")
-}

