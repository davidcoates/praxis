module Main where

import           Common
import qualified Env.Env              as Env
import qualified Env.LEnv             as LEnv
import           Inbuilts             (initialState)
import           Interpret
import           Praxis
import           Term
import           Value

import           Control.Lens.Reified (ReifiedLens (..), ReifiedLens')
import           Control.Monad        (void, when)
import           Data.List            (find, intercalate, stripPrefix)
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
  opts xs
  f <- use infile
  case f of
    Nothing -> repl
    Just f  -> file f

data Arg = Arg { short :: String, long :: String, action :: Praxis () }

instance Show Arg where
  show x = ("-" ++ short x ++ " " ++ long x)

args :: [Arg]
args =
  [ Arg "d" "debug" (flags . debug .= True)
  , Arg "i" "interactive" (flags . interactive .= True)
  , Arg "h" "help" help
  ]

help :: Praxis ()
help = Praxis.abort helpStr where
  helpStr :: String
  helpStr = "usage: praxis [infile] [-o outfile] [OPTION]...\n\n" ++ unlines (map show args)

opts :: [String] -> Praxis ()
opts (x : xs)
  | x == "-o" = case xs of
    (y:ys) -> do
      f <- use outfile
      case f of
        Nothing -> (outfile .= Just y) >> opts ys
        Just _  -> throw "multiple outfile"
    []     -> throw "missing argument to -o"
  | ('-':_) <- x = do
    let opt = find (\a -> ("-" ++ short a) == x) args
    case opt of
      Just a  -> action a >> opts xs
      Nothing -> throw (pretty "unknown option " <> quote (pretty x))
  | otherwise = do
    f <- use infile
    case f of
      Nothing -> (infile .= Just x) >> opts xs
      Just _  -> throw "multiple infile"
opts [] = return ()

file :: String -> Praxis ()
file f = (interpretFile f :: Praxis (Annotated Program, ())) >> onFileSuccess
  where onFileSuccess = use (flags . interactive) >>= (\i -> if i then repl else runMain)

runMain :: Praxis ()
runMain = do
  ty <- tEnv `uses` LEnv.lookup "main"
  case ty of Nothing -> throw "missing main function"
             Just (_ :< Forall [] [] (_ :< TyFun (_ :< TyUnit) (_ :< TyUnit))) ->
               do { Just (Fun f) <- vEnv `uses` Env.lookup "main"; f Value.Unit; return () }
             Just ty -> throwAt (view source ty) $ pretty "main function has bad type " <> quote (pretty ty) <> pretty ", expected () -> ()"

repl :: Praxis ()
repl = forever $ do
  liftIO (putStr "> " >> hFlush stdout)
  liftIO getLine >>= eval

eval :: String -> Praxis ()
eval s = do
  -- TODO fix this so we can have declarations
  (_, v) <- interpret s :: Praxis (Annotated Exp, Value)
  liftIO $ print v

