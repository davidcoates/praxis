module Parse.Desugar.Infix
  ( Assoc(..)
  , Fixity(..)
  ) where

data Assoc = Leftfix | Rightfix | Nonfix deriving Eq

instance Show Assoc where
  show Leftfix  = "infixl"
  show Rightfix = "infixr"
  show Nonfix   = "infix"

newtype Fixity = Fixity { fixity :: (Int, Assoc) }

instance Show Fixity where
  show (Fixity (p, a)) = "[" ++ show a ++ " " ++ show p ++ "]"
