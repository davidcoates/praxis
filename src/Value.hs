module Value
  ( Value(..)
  , len
  , toString
  , fromString
  , readArray
  , writeArray
  ) where

import {-# SOURCE #-} Praxis        (Praxis, liftIOUnsafe)

import           Common
import           Data.Array.IO (IOArray)
import qualified Data.Array.IO as ArrayIO

type Array = IOArray Int Value

data Value = Con Name (Maybe Value)
           | Fun (Value -> Praxis Value)
           | Int Int
           | Bool Bool
           | Char Char
           | Array Array
           | Pair Value Value
           | Unit

toString :: Array -> Praxis String
toString a = liftIOUnsafe $ do
  es <- ArrayIO.getElems a
  return $ map (\(Char c) -> c) es

fromString :: String -> Praxis Array
fromString s = liftIOUnsafe (ArrayIO.newListArray (0, length s - 1) (map Char s))

len :: Array -> Praxis Int
len a = liftIOUnsafe (snd <$> ArrayIO.getBounds a)

readArray :: Array -> Int -> Praxis Value
readArray a i = liftIOUnsafe (ArrayIO.readArray a i)

writeArray :: Array -> Int -> Value -> Praxis ()
writeArray a i e = liftIOUnsafe (ArrayIO.writeArray a i e)

instance Show Value where
  show v = case v of
    Con n v  -> (n ++) $ case v of
      Just x  -> " " ++ show x
      Nothing -> ""
    Fun f    -> "<function>"
    Int i    -> show i
    Bool b   -> show b
    Char c   -> show c
    Array a  -> "<array>"
    Pair a b -> "(" ++ show a ++ ", " ++ show b ++ ")"
    Unit     -> "()"
