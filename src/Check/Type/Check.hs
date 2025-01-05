module Check.Type.Check
  ( run
  ) where

import qualified Check.Type.Generate as Generate
import qualified Check.Type.Solve    as Solve
import           Common
import           Introspect
import           Praxis
import           Stage
import           Term

run :: Term a => Annotated a -> Praxis (Annotated a)
run term = save stage $ do
  stage .= TypeCheck
  term <- Generate.run term >>= Solve.run
  display "checked term" term `ifFlag` debug
  return term
