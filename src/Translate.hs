module Translate
  ( translate
  ) where

import           Common
import           Introspect
import           Praxis
import           Stage
import           Term
import qualified Translate.Reduce as Reduce

translate :: Term a => Annotated a -> Praxis (Annotated a)
translate term = save stage $ do
  stage .= Translate
  clearTerm `ifFlag` debug
  term <- Reduce.run term
  return term

