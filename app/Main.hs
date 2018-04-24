module Main where

import Compiler
import Interpret

main :: IO ()
main = do
  (x, _) <- run single
  case x of
    Left e  -> print e
    Right x -> putStrLn "Success"

single :: Compiler ()
single = do
  liftIO $ putStrLn "Enter expression: "
  x <- liftIO $ getLine
  set src x
  interpret

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
