module Main where

import           Common
import qualified Env.Env            as Env
import qualified Env.LEnv           as LEnv
import           Executors
import           Inbuilts           (initialState)
import           Praxis
import           Term
import           Value

import           Control.Monad      (void, when)
import           Data.List          (delete)
import           System.Environment
import           System.IO

main :: IO ()
main = hSetBuffering stdin LineBuffering >> do
  args <- getArgs
  void $ runPraxis (parse args) initialState

data Mode = Interactive (Maybe FilePath)
          | Interpret FilePath
          | Translate FilePath

-- TODO could use a State monad but doesn't play nicely with the Praxis monad
parseFilename :: [String] -> Praxis ([String], Maybe FilePath)
parseFilename args = return $ case args of
  (('-':_):_) -> (args, Nothing)
  (file:args) -> (args, Just file)
  _           -> (args, Nothing)

parseHelp :: [String] -> Praxis [String]
parseHelp args = if "-h" `elem` args then help else return args

parseDebug :: [String] -> Praxis [String]
parseDebug args = if "-d" `elem` args
  then do
    flags . debug .= True
    return (delete "-d" args)
  else return args

parseInteractive :: [String] -> Praxis ([String], Bool)
parseInteractive args = if "-i" `elem` args
  then return (delete "-i" args, True)
  else return (args, False)

parseTranslate :: [String] -> Praxis ([String], Bool)
parseTranslate args = if "-t" `elem` args
  then return (delete "-t" args, True)
  else return (args, False)

parseOpts :: [String] -> Praxis Mode
parseOpts args = do
  (args, file) <- parseFilename args
  args <- parseHelp args
  args <- parseDebug args
  (args, interactive) <- parseInteractive args
  (args, translate) <- parseTranslate args
  when (not (null args)) $ throw (pretty "unknown option " <> quote (pretty (unwords args)))
  case (interactive, translate) of
    (True, True)   -> throw (pretty "at most one of -i and -t can be specified")
    (True, False)  -> case file of
      Just file -> return (Translate file)
      Nothing   -> throw (pretty "missing file (translate mode)")
    (False, True) -> return (Interactive file)
    (False, False) -> case file of
      Just file -> return (Interpret file)
      Nothing   -> throw (pretty "missing file (interpret mode)")

parse :: [String] -> Praxis ()
parse xs = do
  mode <- parseOpts xs
  case mode of
    Interactive file -> do
      case file of
        Just file -> do
          text <- liftIO (readFile file)
          interpretProgram text
          repl
        Nothing   -> repl
    Interpret file -> do
      text <- liftIO (readFile file)
      interpretProgram text
      runMain
    Translate file -> do
      text <- liftIO (readFile file)
      translation <- translateProgram text
      -- TODO write to out file
      liftIO (putStr translation)

help :: Praxis a
help = Praxis.abort helpStr where
  helpStr = "usage: praxis [infile] [OPTION]...\n\n" ++ unlines helpOpts
  helpOpts =
    [ "-d debug"
    , "-i interactive"
    , "-h help"
    , "-t translate" ]

runMain :: Praxis ()
runMain = do
  ty <- tEnv `uses` LEnv.lookup "main"
  case ty of Nothing -> throw "missing main function"
             Just (_ :< Forall [] [] (_ :< TyFun (_ :< TyUnit) (_ :< TyUnit))) ->
               do { Just (Fun f) <- vEnv `uses` Env.lookup "main"; f Value.Unit; return () }
             Just ty -> throwAt (view source ty) $ pretty "main function has bad type " <> quote (pretty ty) <> pretty ", expected () -> ()"

forever :: Praxis a -> Praxis a
forever p = try p >> forever p

repl :: Praxis ()
repl = forever $ do
  liftIO (putStr "> " >> hFlush stdout)
  liftIO getLine >>= eval

eval :: String -> Praxis ()
eval s = do
  -- TODO fix this so we can have declarations
  v <- interpretExp s
  liftIO $ print v

