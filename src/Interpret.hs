module Interpret
  ( interpret
  , interpretFile
  ) where

import           Check
import           Eval
import           Parse
import           Praxis

interpret :: String -> Praxis ()
interpret s = do
  set src s
  parse
  check
  eval

interpretFile :: FilePath -> Praxis ()
interpretFile f = do
  set filename f
  s <- liftIO (readFile f)
  set src s
  parse
  check
  eval
