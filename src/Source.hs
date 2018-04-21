module Source
  ( Pos(..)
  , Source(..)
  , Sourced(..)
  , formatSpelling
  , showStart
  , showEnd
  , showSpelling
  ) where

import Control.Applicative

data Pos = Pos { line :: Int, column :: Int }

data Sourced a = Sourced { source :: Source, value :: a }

data Source = Source { start :: Pos, end :: Pos, spelling :: String }
            | Phony

lift :: (Source -> String) -> Source -> String
lift f Phony = "\x26A1\x26A1\x26A1PHONY\x26A1\x26A1\x26A1"
lift f s     = f s

showStart :: Source -> String
showStart = lift (show . start)

showEnd :: Source -> String
showEnd = lift (show . end)

formatSpelling :: String -> String
formatSpelling x = "\x25B7" ++ x ++ "\x25C1"

showSpelling :: Source -> String
showSpelling = lift (formatSpelling . spelling)

instance Show Pos where
  show p = show (line p) ++ ":" ++ show (column p)

instance Show Source where
  show s = showSpelling s ++ " @ " ++ showStart s

instance Functor Sourced where
  fmap f x = x { value = f (value x) }

instance Applicative Sourced where
  pure x = Sourced { source = mempty, value = x }
  liftA2 f x y = Sourced { source = mappend (source x) (source y), value = f (value x) (value y) }

instance Monoid Source where
  mempty = Phony
  mappend Phony s = s
  mappend s Phony = s
  mappend s1 s2   = Source { start = start s1, end = end s2, spelling = spelling s1 ++ spelling s2 }
