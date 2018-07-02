module Main where

import           AST
import           Check.AST            (Annotated)
import           Inbuilts             (initialState)
import           Interpret
import           Praxis
import           Pretty               (indent)
import           Value

import           Control.Lens.Reified (ReifiedLens (..), ReifiedLens')
import           Control.Monad        (void, when)
import           Data.List            (stripPrefix)
import           System.Environment
import           System.IO

pretty :: Praxis a -> Praxis b -> Praxis b -> Praxis b
pretty c f g = try c (\e -> liftIO (print e >> putStrLn "^^^ ERRORS OCCURED ^^^") >> f) (const g)

forever :: Praxis a -> Praxis a
forever c = pretty c (forever c) (forever c)

main :: IO ()
main = hSetBuffering stdin LineBuffering >> do
  args <- getArgs
  void $ run (parse args) initialState

parse :: [String] -> Praxis ()
parse []  = repl
parse ("-l":x:xs) | x == "debug" = set (flags . level) Debug >> parse xs
                  | x == "trace" = set (flags . level) Trace >> parse xs
parse [f] = file f
parse _   = liftIO $ putStrLn "Too many arguments"

file :: String -> Praxis ()
file f = pretty (interpretFile f :: Praxis (Annotated Program, ())) (return ()) repl

repl :: Praxis ()
repl = forever $ do
  s <- liftIO ( putStr "> " >> hFlush stdout >> getLine )
  case s of
    ':' : cs -> meta cs
    _        -> eval s

eval :: String -> Praxis ()
eval s = do
  -- TODO fix this so we can have declarations
  (_, v) <- interpret s :: Praxis (Annotated Exp, Value)
  liftIO $ print v

meta :: String -> Praxis ()
meta "?" = liftIO $ putStrLn "help is TODO"
meta s = liftIO $ putStrLn ("unknown command ':" ++ s ++ "'\nuse :? for help.")
