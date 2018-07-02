module Main where

import qualified Env.VEnv             as VEnv (lookup)
import           Inbuilts             (initialState)
import           Interpret
import           Praxis
import           Pretty               (indent)

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
parse []          = repl
parse [f]         = file f
parse ("-d":args) = set (flags . debug) True >> parse args
parse _           = liftIO $ putStrLn "Too many arguments"

file :: String -> Praxis ()
file f = pretty (interpretFile f) (return ()) repl

repl :: Praxis ()
repl = forever $ do
  s <- liftIO ( putStr "> " >> hFlush stdout >> getLine )
  case s of
    ':' : cs -> meta cs
    _        -> eval s

eval :: String -> Praxis ()
eval s = do
  let s' = "repl___ = " ++ s -- TODO fix this so we can have declarations
  interpret s'
  Just v <- VEnv.lookup "repl___"
  liftIO $ print v

meta :: String -> Praxis ()
meta "?" = liftIO $ putStrLn "help is TODO"
meta s | Just s <- stripPrefix "toggle " s = case parseFlag s of
  Just (Lens l) -> do
    b <- get l
    set l (not b)
    return ()
  Nothing -> liftIO $ putStrLn ("unknown flag '" ++ s ++ "'")
meta s = liftIO $ putStrLn ("unknown command ':" ++ s ++ "'\nuse :? for help.")

parseFlag :: String -> Maybe (ReifiedLens' PraxisState Bool)
parseFlag "debug" = Just $ Lens $ flags . debug
parseFlag _       = Nothing
