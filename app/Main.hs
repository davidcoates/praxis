module Main where

main = putStrLn "Hey!"

{-
import Parse
import Check
import CodeGen

wrap :: Show a => Either a b -> Either (IO ()) b
wrap (Left x)  = Left (print x)
wrap (Right y) = Right y

main :: IO ()
main = do
  putStrLn "Enter expression to compile:"
  x <- getLine
  case compile x of Left x  -> x
                    Right y -> putStr y

compile :: String -> Either (IO ()) String
compile x = do
  y <- wrap (parse x) >>= wrap . infer
  return (codeGen y)
-}
