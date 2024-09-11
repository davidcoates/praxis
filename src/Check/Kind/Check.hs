module Check.Kind.Check
  ( check
  ) where

import           Check.Kind.Generate as Generate
import           Check.Kind.Rename   as Rename
import           Check.Kind.Solve    as Solve
import           Common
import           Introspect
import           Praxis
import           Stage
import           Term

check :: Term a => Annotated a -> Praxis (Annotated a)
check term = save stage $ do
  stage .= KindCheck
  term <- Rename.run term >>= Generate.run >>= Solve.run
  display "checked term" term `ifFlag` debug
  return term
