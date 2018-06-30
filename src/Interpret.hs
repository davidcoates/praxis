module Interpret
  ( interpret
  , interpretFile
  ) where

import           Check
import           Compiler
import           Eval
import           Parse

interpret :: String -> Compiler ()
interpret s = do
  set src s
  parse
  check
  eval

interpretFile :: FilePath -> Compiler ()
interpretFile f = do
  set filename f
  s <- liftIO (readFile f)
  set src s
  parse
  check
  eval
