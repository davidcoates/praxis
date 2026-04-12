module Check.Kind.Check
  ( run
  ) where

import qualified Check.Kind.Generate as Generate
import qualified Check.Kind.Solve    as Solve
import           Check.Kind.State
import           Common
import           Control.Monad.State (runStateT)
import           Introspect
import           Praxis
import           Stage
import           Term

run :: IsTerm a => Annotated Parse a -> Praxis (Annotated KindCheck a)
run term = do
  (term, _) <- runStateT (Generate.run term >>= Solve.run) emptyKindLocal
  display KindCheck "checked term" term `ifFlag` debug
  return term
