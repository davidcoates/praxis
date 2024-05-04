module Main where

import           Common
import qualified Env.Env            as Env
import qualified Env.LEnv           as LEnv
import           Inbuilts           (initialState)
import           Interpret
import           Praxis
import           Term

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
          | Compile FilePath

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

parseCompile :: [String] -> Praxis ([String], Bool)
parseCompile args = if "-c" `elem` args
  then return (delete "-c" args, True)
  else return (args, False)

parseOpts :: [String] -> Praxis Mode
parseOpts args = do
  (args, file) <- parseFilename args
  args <- parseHelp args
  args <- parseDebug args
  (args, interactive) <- parseInteractive args
  (args, compile) <- parseCompile args
  when (not (null args)) $ throw (pretty "unknown option " <> quote (pretty (unwords args)))
  case (interactive, compile) of
    (True, True)   -> throw (pretty "at most one of -i and -c can be specified")
    (False, True)  -> case file of
      Just file -> return (Compile file)
      Nothing   -> throw (pretty "missing file (compile mode)")
    (True, False) -> return (Interactive file)
    (False, False) -> case file of
      Just file -> return (Interpret file)
      Nothing   -> throw (pretty "missing file (interpret mode)")

parse :: [String] -> Praxis ()
parse xs = return () -- TODO
{-
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
      intepretProgram text
    Compile file -> do
      text <- liftIO (readFile file)
      let outFile = dropExtension file
      error "TODO" -- FIXME
-}

help :: Praxis a
help = Praxis.abort helpStr where
  helpStr = "usage: praxis [infile] [OPTION]...\n\n" ++ unlines helpOpts
  helpOpts =
    [ "-d debug"
    , "-i interactive"
    , "-h help"
    , "-c compile" ]

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
