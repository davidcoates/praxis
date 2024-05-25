module Check.Type.Check
  ( check
  ) where

import           Check.Type.Generate as Generate
import           Check.Type.Rename   as Rename
import           Check.Type.Solve    as Solve
import           Common
import           Introspect
import           Praxis
import           Stage
import           Term

check :: Term a => Annotated a -> Praxis (Annotated a)
check term = save stage $ do
  stage .= TypeCheck
  term <- Rename.run term >>= Generate.run >>= Solve.run
  display term `ifFlag` debug
  return term
