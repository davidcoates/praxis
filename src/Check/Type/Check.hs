{-# LANGUAGE DataKinds #-}

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

run :: IsTerm a => Annotated KindCheck a -> Praxis (Annotated TypeCheck a)
run term = do
  term <- Generate.run term >>= Solve.run
  display TypeCheck "checked term" term `ifFlag` debug
  return term
