{-# LANGUAGE GADTs               #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Check.Type.Check
  ( check
  ) where

import           Check.Type.Generate as Generate
import           Check.Type.Require
import           Check.Type.Solve    as Solve
import           Check.Type.System
import           Common
import           Introspect
import           Praxis
import           Stage
import           Term

check :: Term a => Annotated a -> Praxis (Annotated a)
check term = save stage $ do
  stage .= TypeCheck Warmup
  our .= initialSystem
  term <- Generate.run term
  term <- Solve.run term
  display term `ifFlag` debug
  return term
