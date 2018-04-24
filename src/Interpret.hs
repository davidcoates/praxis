module Interpret
  ( interpret
  ) where

import Compiler
import Parse
import Check

interpret :: Compiler () -- TODO
interpret = parse >> check
  
