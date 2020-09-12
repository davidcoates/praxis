module Main where

import           Common
import           Env
import           Inbuilts             (initialState)
import           Interpret
import           Praxis
import           Term
import           Value

import           Control.Lens.Reified (ReifiedLens (..), ReifiedLens')
import           Control.Monad        (void, when)
import           Data.List            (find, intercalate, stripPrefix)
import           Prelude              hiding (lookup)
import           System.Environment
import           System.IO

forever :: Praxis a -> Praxis a
forever p = try p >> forever p

main :: IO ()
main = hSetBuffering stdin LineBuffering >> do
  args <- getArgs
  void $ runPraxis (parse args) initialState

parse :: [String] -> Praxis ()
parse xs = do
  xs <- opts xs
  case xs of
    []  -> repl
    [f] -> file f
    _   -> liftIO $ putStrLn "Too many arguments"

data Arg = Arg { short :: String, long :: String, action :: Praxis () } -- TODO use long e.g., for help

args :: [Arg]
args =
  [ Arg "d" "debug" (flags . debug .= True)
  , Arg "i" "interactive" (flags . interactive .= True)
  ]

opts :: [String] -> Praxis [String]
opts (x:xs)
  | Just a <- find (\a -> ("-" ++ short a) == x) args = action a >> opts xs
  | otherwise                                         = (x:) <$> opts xs
opts []  = return []

file :: String -> Praxis ()
file f = (interpretFile f :: Praxis (Annotated Program, ())) >> onFileSuccess
  where onFileSuccess = use (flags . interactive) >>= (\i -> if i then repl else runMain)

runMain :: Praxis ()
runMain = do
  t <- tEnv `uses` lookup "main"
  case t of Nothing -> throw "missing main function"
            Just (_ :< Mono (_ :< TyFun (_ :< TyUnit) (_ :< TyUnit))) ->
              do { Just (F f) <- vEnv `uses` lookup "main"; f U; return () }
            Just t -> throwAt (view source t) $ pretty "main function has bad type " <> quote (pretty t) <> pretty ", expected () -> ()"

repl :: Praxis ()
repl = forever $ do
  liftIO (putStr "> " >> hFlush stdout)
  liftIO getLine >>= eval

eval :: String -> Praxis ()
eval s = do
  -- TODO fix this so we can have declarations
  (_, v) <- interpret s :: Praxis (Annotated Exp, Value)
  liftIO $ print v

