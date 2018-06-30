module Value
  ( Value(..)
  ) where

import           AST      (Lit)
import {-# SOURCE #-} Compiler
import           Record

data Value = L Lit
           | R (Record Value)
           | F (Value -> Compiler Value)

instance Show Value where
  show (L l) = show l
  show (R r) = show r
  show (F f) = "<function>"
