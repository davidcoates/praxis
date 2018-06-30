module Main where

import           Compiler
import qualified Env.VEnv             as VEnv (lookup)
import           Inbuilts             (initialState)
import           Interpret
import           Pretty               (indent)

import           Control.Lens.Reified (ReifiedLens (..), ReifiedLens')
import           Control.Monad        (void, when)
import           Data.List            (stripPrefix)
import           System.Environment
import           System.IO

pretty :: Compiler a -> Compiler b -> Compiler b -> Compiler b
pretty c f g = try c (\e -> liftIO (print e >> putStrLn "^^^ ERRORS OCCURED ^^^") >> f) (const g)

forever :: Compiler a -> Compiler a
forever c = pretty c (forever c) (forever c)

main :: IO ()
main = hSetBuffering stdin LineBuffering >> do
  args <- getArgs
  void $ run (parse args) initialState

parse :: [String] -> Compiler ()
parse []          = repl
parse [f]         = file f
parse ("-d":args) = set (flags . debug) True >> parse args
parse _           = liftIO $ putStrLn "Too many arguments"

file :: String -> Compiler ()
file f = pretty (interpretFile f) (return ()) repl

repl :: Compiler ()
repl = forever $ do
  s <- liftIO ( putStr "> " >> hFlush stdout >> getLine )
  case s of
    ':' : cs -> meta cs
    _        -> eval s

eval :: String -> Compiler ()
eval s = do
  let s' = "repl___ = " ++ s -- TODO fix this so we can have declarations
  interpret s'
  Just v <- VEnv.lookup "repl___"
  liftIO $ print v

meta :: String -> Compiler ()
meta "?" = liftIO $ putStrLn "help is TODO"
meta s | Just s <- stripPrefix "toggle " s = case parseFlag s of
  Just (Lens l) -> do
    b <- get l
    set l (not b)
    return ()
  Nothing -> liftIO $ putStrLn ("unknown flag '" ++ s ++ "'")
meta s = liftIO $ putStrLn ("unknown command ':" ++ s ++ "'\nuse :? for help.")

parseFlag :: String -> Maybe (ReifiedLens' CompilerState Bool)
parseFlag "debug" = Just $ Lens $ flags . debug
parseFlag _       = Nothing
