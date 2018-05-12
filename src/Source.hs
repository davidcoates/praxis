module Source
  ( Pos(..)
  , Source(..)
  ) where

data Pos = Pos { line :: Int, column :: Int }

data Source = Source { start :: Pos, end :: Pos, spelling :: String }
            | Phantom -- ^Used for phantom tokens e.g., layout tokens inserted by the tokeniser

instance Show Pos where
  show p = show (line p) ++ ":" ++ show (column p)

instance Show Source where
  show Phantom = "?"
  show s       = show (start s)
--  show s       = show (start s) ++ " " ++ sanitise (show (spelling s))
--    where sanitise xs = if length xs < 30 then xs else take 30 xs ++ "..."


instance Monoid Source where
  mempty = Phantom
  mappend Phantom s = s
  mappend s Phantom = s
  mappend s1     s2 = Source { start = start s1, end = end s2, spelling = spelling s1 ++ spelling s2 }
