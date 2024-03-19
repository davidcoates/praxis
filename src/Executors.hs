module Executors
  ( interpretExp
  , interpretProgram
  , translateProgram
  ) where

import           Check  (check)
import           Common
import qualified Eval
import           Parse  (parse)
import           Praxis
import           Term
import qualified Translate
import           Value  (Value)

interpretExp :: String -> Praxis Value
interpretExp text = do
  e <- parse text >>= check :: Praxis (Annotated Exp)
  v <- Eval.runExp e
  return v

interpretProgram :: String -> Praxis (Annotated Program)
interpretProgram text = do
  p <- parse text >>= check :: Praxis (Annotated Program)
  () <- Eval.runProgram p
  return p

translateProgram :: String -> Praxis String
translateProgram text = do
  p <- parse text >>= check :: Praxis (Annotated Program)
  t <- Translate.runProgram p
  return t

