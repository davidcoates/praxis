module Check.Kind.Check
  ( run
  ) where

import qualified Check.Kind.Generate as Generate
import qualified Check.Kind.Solve    as Solve
import           Common
import           Introspect
import           Praxis
import           Stage
import           Term

run :: IsTerm a => Annotated Parse a -> Praxis (Annotated KindCheck a)
run term = do
  term <- Generate.run term >>= Solve.run
  display KindCheck "checked term" term `ifFlag` debug
  return term
