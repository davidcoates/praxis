{-# LANGUAGE DataKinds #-}

module Eval.Value
  ( Value(..)
  , integerToValue
  , valueToInteger
  , lenArray
  , readArray
  , writeArray
  , newArray
  ) where

import {-# SOURCE #-}           Praxis           (Praxis, liftIOUnsafe)
import                          Stage
import                          Term             (Specialization)

import                          Common
import                          Data.Array.IO    (IOArray)
import                qualified Data.Array.IO    as ArrayIO
import                          System.IO.Unsafe (unsafePerformIO)


type Array = IOArray USize Value

data Value
  = Array Array
  | Bool Bool
  | Char Char
  | Data Name Value
  | Enum Name
  | Fn (Value -> Praxis Value)
  | I8 I8
  | I16 I16
  | I32 I32
  | I64 I64
  | ISize ISize
  | Pair Value Value
  | Polymorphic (Specialization Monomorphize -> Value)
  | String String
  | U8 U8
  | U16 U16
  | U32 U32
  | U64 U64
  | USize USize
  | Unit

integerToValue :: Name -> Integer -> Value
integerToValue n = case n of
  "I8"    -> I8    . fromInteger
  "I16"   -> I16   . fromInteger
  "I32"   -> I32   . fromInteger
  "I64"   -> I64   . fromInteger
  "ISize" -> ISize . fromInteger
  "U8"    -> U8    . fromInteger
  "U16"   -> U16   . fromInteger
  "U32"   -> U32   . fromInteger
  "U64"   -> U64   . fromInteger
  "USize" -> USize . fromInteger

valueToInteger :: Value -> Integer
valueToInteger v = case v of
  I8    v -> toInteger v
  I16   v -> toInteger v
  I32   v -> toInteger v
  I64   v -> toInteger v
  ISize v -> toInteger v
  U8    v -> toInteger v
  U16   v -> toInteger v
  U32   v -> toInteger v
  U64   v -> toInteger v
  USize v -> toInteger v

lenArray :: Array -> Praxis USize
lenArray a = liftIOUnsafe (snd <$> ArrayIO.getBounds a)

readArray :: Array -> USize -> Praxis Value
readArray a i = liftIOUnsafe (ArrayIO.readArray a i)

writeArray :: Array -> USize -> Value -> Praxis ()
writeArray a i e = liftIOUnsafe (ArrayIO.writeArray a i e)

newArray :: USize -> Value -> Praxis Value
newArray i v = liftIOUnsafe (Array <$> ArrayIO.newArray (0, i) v)

instance Show Value where
  show value = case value of
    Array a       -> let vs = unsafePerformIO (ArrayIO.getElems a) in "[" ++ intercalate ", " (map show vs) ++ "]" -- eek!
    Bool b        -> show b
    Char c        -> show c
    Data n v      -> n ++ " " ++ show v
    Enum n        -> n
    Fn f          -> "«function»"
    Pair a b      -> "(" ++ show a ++ ", " ++ show b ++ ")"
    Polymorphic _ -> "«polymorphic»"
    String s      -> show s
    I8 i          -> show i
    I16 i         -> show i
    I32 i         -> show i
    I64 i         -> show i
    ISize i       -> show i
    U8 i          -> show i
    U16 i         -> show i
    U32 i         -> show i
    U64 i         -> show i
    USize i       -> show i
    Unit          -> "()"
