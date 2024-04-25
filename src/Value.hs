module Value
  ( Value(..)
  , lenArray
  , readArray
  , writeArray
  , newArray
  ) where

import {-# SOURCE #-}           Praxis           (Praxis, liftIOUnsafe)

import                          Common
import                          Data.Array.IO    (IOArray)
import                qualified Data.Array.IO    as ArrayIO
import                          Data.Int
import                          Data.Word
import                          System.IO.Unsafe (unsafePerformIO)

type Array = IOArray Int Value

data Value = Array Array
           | Bool Bool
           | Char Char
           | Data Name Value
           | Enum Name
           | Fun (Value -> Praxis Value)
           | I8    Int8
           | I16   Int16
           | I32   Int32
           | I64   Int64
           | ISize Int64
           | Pair Value Value
           | String String
           | U8    Word8
           | U16   Word16
           | U32   Word32
           | U64   Word64
           | USize Word64
           | Unit

lenArray :: Array -> Praxis Int
lenArray a = liftIOUnsafe (snd <$> ArrayIO.getBounds a)

readArray :: Array -> Int -> Praxis Value
readArray a i = liftIOUnsafe (ArrayIO.readArray a i)

writeArray :: Array -> Int -> Value -> Praxis ()
writeArray a i e = liftIOUnsafe (ArrayIO.writeArray a i e)

newArray :: Int -> Value -> Praxis Value
newArray i v = liftIOUnsafe (Array <$> ArrayIO.newArray (0, i) v)

instance Show Value where
  show value = case value of
    Array a  -> let vs = unsafePerformIO (ArrayIO.getElems a) in "[" ++ intercalate ", " (map show vs) ++ "]" -- eek!
    Bool b   -> show b
    Char c   -> show c
    Data n v -> n ++ " " ++ show v
    Enum n   -> n
    Fun f    -> "«function»"
    Pair a b -> "(" ++ show a ++ ", " ++ show b ++ ")"
    String s -> show s
    I8     i -> show i
    I16    i -> show i
    I32    i -> show i
    I64    i -> show i
    ISize  i -> show i
    U8     i -> show i
    U16    i -> show i
    U32    i -> show i
    U64    i -> show i
    USize  i -> show i
    Unit     -> "()"
