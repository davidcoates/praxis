module Check.Kind.Check
  ( run
  ) where

import qualified Check.Kind.Generate as Generate
import qualified Check.Kind.Rename   as Rename
import qualified Check.Kind.Solve    as Solve
import           Common
import           Introspect
import           Praxis
import           Stage
import           Term

run :: Term a => Annotated a -> Praxis (Annotated a)
run term = save stage $ do
  stage .= KindCheck
  term <- Rename.run term >>= Generate.run >>= Solve.run
  display "checked term" term `ifFlag` debug
  return term
