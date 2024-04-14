module Value
  ( Value(..)
  , len
  , readArray
  , writeArray
  ) where

import {-# SOURCE #-}           Praxis           (Praxis, liftIOUnsafe)

import                          Common
import                          Data.Array.IO    (IOArray)
import                qualified Data.Array.IO    as ArrayIO
import                          System.IO.Unsafe (unsafePerformIO)

type Array = IOArray Int Value

data Value = Data Name Value
           | Enum Name
           | Fun (Value -> Praxis Value)
           | Int Int
           | Bool Bool
           | Char Char
           | String String
           | Array Array
           | Pair Value Value
           | Unit

len :: Array -> Praxis Int
len a = liftIOUnsafe (snd <$> ArrayIO.getBounds a)

readArray :: Array -> Int -> Praxis Value
readArray a i = liftIOUnsafe (ArrayIO.readArray a i)

writeArray :: Array -> Int -> Value -> Praxis ()
writeArray a i e = liftIOUnsafe (ArrayIO.writeArray a i e)

showValue :: Value -> IO String
showValue = \case
  Data n v -> ((n ++ " ") ++) <$> showValue v
  Enum n   -> return n
  Fun f    -> return "<function>"
  Int i    -> return (show i)
  Bool b   -> return (show b)
  Char c   -> return (show c)
  String s -> return (show s)
  Array a  -> do
    vs <- ArrayIO.getElems a
    vs' <- mapM showValue vs
    return ("[" ++ intercalate ", " vs' ++ "]")
  Pair a b -> (\a b -> "(" ++ a ++ ", " ++ b ++ ")") <$> showValue a <*> showValue b
  Unit     -> return "()"

instance Show Value where
  show v = unsafePerformIO (showValue v) -- eek!
