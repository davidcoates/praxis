module Value
  ( Value(..)
  ) where

import           Common
import {-# SOURCE #-} Praxis (Praxis)
import           Term   (Lit)

-- TODO change the constructor names
data Value = C Name [Value]
           | F (Value -> Praxis Value)
           | L Lit
           | P Value Value
           | U

instance Show Value where
  show v = case v of
    C n vs -> n ++ concat (map (\x -> " " ++ showParen x) vs) where
      showParen x@(C _ (_:_)) = "(" ++ show x ++ ")"
      showParen x             = show x
    F f    -> "<function>"
    L l    -> show l
    P a b  -> "(" ++ show a ++ ", " ++ show b ++ ")"
    U      -> "()"
