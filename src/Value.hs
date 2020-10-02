module Value
  ( Value(..)
  ) where

import           Common
import {-# SOURCE #-} Praxis (Praxis)
import           Term   (Lit)

-- TODO change the constructor names
data Value = C Name (Maybe Value)
           | F (Value -> Praxis Value)
           | L Lit
           | P Value Value
           | U

instance Show Value where
  show v = case v of
    C n v -> (n ++) $ case v of
      Just x  -> " " ++ show x
      Nothing -> ""
    F f    -> "<function>"
    L l    -> show l
    P a b  -> "(" ++ show a ++ ", " ++ show b ++ ")"
    U      -> "()"
