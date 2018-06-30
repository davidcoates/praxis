module Main where

import           Compiler
import           Interpret
import           System.Environment
import           System.IO

forever :: Monad m => m a -> m b
forever m = m >> forever m

pretty :: Compiler () -> IO ()
pretty c = do
  (x, _) <- run c
  case x of
    Left e  -> print e >> putStrLn "^^^ ERRORS OCCURED ^^^"
    Right _ -> return ()

main :: IO ()
main = do
  args <- getArgs
  case args of
    []  -> forever single
    [f] -> pretty (interpretFile f)
    _   -> putStrLn "Too many arguments"

single :: IO ()
single = do
  putStr "> "
  hFlush stdout
  s <- getLine
  pretty (interpret s)
