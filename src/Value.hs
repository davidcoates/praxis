module Value
  ( Value(..)
  ) where

import {-# SOURCE #-} Praxis (Praxis)
import           Record
import           Term   (Lit)

data Value = L Lit
           | R (Record Value)
           | F (Value -> Praxis Value)

instance Show Value where
  show (L l) = show l
  show (R r) = show r
  show (F f) = "<function>"
