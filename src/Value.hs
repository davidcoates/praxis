module Value
  ( Value(..)
  ) where

import AST (Lit)
import Record
import {-# SOURCE #-} Compiler

data Value = U
           | L Lit
           | R (Record Value)
           | F (Value -> Compiler Value)

instance Show Value where
  show U     = "()"
  show (L l) = show l
  show (R r) = show r
  show (F f) = "<function>"
