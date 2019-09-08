module Value
  ( Value(..)
  ) where

import {-# SOURCE #-} Praxis (Praxis)
import           Common
import           Record
import           Term   (Lit)

data Value = C Name [Value]
           | L Lit
           | R (Record Value)
           | F (Value -> Praxis Value)

instance Show Value where
  show v = case v of
    C n vs -> n ++ concat (map (\x -> " " ++ showParen x) vs) where
      showParen x@(C _ (_:_)) = "(" ++ show x ++ ")"
      showParen x             = show x
    L l    -> show l
    R r    -> show r
    F f    -> "<function>"
