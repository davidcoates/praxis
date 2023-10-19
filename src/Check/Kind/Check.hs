module Check.Kind.Check
  ( check
  ) where

import           Check.Kind.Generate as Generate
import           Check.Kind.Require
import           Check.Kind.Solve    as Solve
import           Check.Kind.System
import           Common
import           Introspect
import           Praxis
import           Stage
import           Term

check :: Term a => Annotated a -> Praxis (Annotated a)
check term = save stage $ do
  stage .= KindCheck Warmup
  our .= initialSystem
  term <- Generate.run term
  term <- Solve.run term
  display term `ifFlag` debug
  return term
