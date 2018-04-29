module Interpret
  ( interpret
  , interpretFile
  ) where

import Compiler
import Parse
import Check

interpret :: String -> Compiler ()
interpret s = do
  set src s
  parse
  check

interpretFile :: FilePath -> Compiler ()
interpretFile f = do
  set filename f
  s <- liftIO (readFile f)  
  set src s
  parse
  check
