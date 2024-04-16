module Check.Type.Check
  ( check
  ) where

import           Check.Type.Generate as Generate
import           Check.Type.Solve    as Solve
import           Common
import           Introspect
import           Praxis
import           Stage
import           Term

check :: Term a => Annotated a -> Praxis (Annotated a)
check term = save stage $ do
  stage .= TypeCheck Warmup
  term <- Generate.run term
  term <- Solve.run term
  display term `ifFlag` debug
  return term
