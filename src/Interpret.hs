module Interpret
  ( interpret
  , interpretFile
  ) where

import Compiler
import Parse
import Check
import Eval

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
