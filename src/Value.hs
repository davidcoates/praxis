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
import           System.IO.Unsafe             (unsafePerformIO)

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

showValue :: Value -> IO String
showValue = \case
  Con n v  -> (n ++) <$> case v of
    Just x  -> (" " ++) <$> showValue x
    Nothing -> return ""
  Fun f    -> return "<function>"
  Int i    -> return (show i)
  Bool b   -> return (show b)
  Char c   -> return (show c)
  Array a  -> do
    vs <- ArrayIO.getElems a
    vs' <- mapM showValue vs
    return ("[" ++ intercalate ", " vs' ++ "]")
  Pair a b -> (\a b -> "(" ++ a ++ ", " ++ b ++ ")") <$> showValue a <*> showValue b
  Unit     -> return "()"

instance Show Value where
  show v = unsafePerformIO (showValue v) -- eek!
