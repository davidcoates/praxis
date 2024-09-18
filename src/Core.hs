module Core
  ( run
  ) where

import           Common
import qualified Core.Lift  as Lift
import qualified Core.Mono  as Mono
import           Introspect
import           Praxis
import           Stage
import           Term

run :: Term a => Annotated a -> Praxis (Annotated a)
run term = save stage $ do
  stage .= Core
  clearTerm `ifFlag` debug
  term <- Lift.run term
  term <- Mono.run term
  return term

