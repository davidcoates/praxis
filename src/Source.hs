module Source
  ( Source(..)
  , formatSpelling
  , showStart
  , showEnd
  , showSpelling
  , Sourced(..)
  ) where

import Control.Applicative
import Pos

data Sourced a = Sourced { source :: Source, value :: a }

instance Functor Sourced where
  fmap f x = x { value = f (value x) }

instance Applicative Sourced where
  pure x = Sourced { source = mempty, value = x }
  liftA2 f x y = Sourced { source = mappend (source x) (source y), value = f (value x) (value y) }


data Source = Source { start :: Pos, end :: Pos, spelling :: String }
            | Phony        

instance Monoid Source where
  mempty = Phony
  mappend Phony s = s
  mappend s Phony = s
  mappend s1 s2   = Source { start = start s1, end = end s2, spelling = spelling s1 ++ spelling s2 } 

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

instance Show Source where
  show s = showSpelling s ++ " @ " ++ showStart s

