module Main where

import Compiler
import Interpret
import System.IO

main :: IO ()
main = single >> main

single :: IO ()
single = do
  putStr "> "
  hFlush stdout
  s <- getLine
  (x, _) <- run (set src s >> interpret)
  case x of
    Left e  -> print e >> putStrLn "^^^ ERRORS OCCURED ^^^"
    Right _ -> return ()

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
