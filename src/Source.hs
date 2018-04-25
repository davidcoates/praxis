module Source
  ( Pos(..)
  , Source(..)
  , showSource
  ) where

data Pos = Pos { line :: Int, column :: Int }

data Source = Source { start :: Pos, end :: Pos, spelling :: String }
            | Phantom -- ^Used for phantom tokens e.g., layout tokens inserted by the tokeniser 

showSource :: ((Pos, Pos, String) -> String) -> Source -> String
showSource _ Phantom = "\x26A1\x26A1\x26A1PHONY\x26A1\x26A1\x26A1"
showSource f s       = f (start s, end s, spelling s)

instance Show Pos where
  show p = show (line p) ++ ":" ++ show (column p)

instance Show Source where
  show = showSource (\(start, end, spelling) -> show start ++ " \x25B7" ++ spelling ++ "\x25C1")

instance Monoid Source where
  mempty = Phantom
  mappend Phantom s = s
  mappend s Phantom = s
  mappend s1     s2 = Source { start = start s1, end = end s2, spelling = spelling s1 ++ spelling s2 }
