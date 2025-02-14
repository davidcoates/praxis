module Main where

import           Common
import           Eval               (runMain)
import           Inbuilts           (runWithPrelude)
import           Introspect
import           Praxis
import           Stage
import           Term
import           Util               (eval)

import           Control.Monad      (void, when)
import           Data.List          (delete)
import           System.Environment
import           System.IO


main :: IO ()
main = hSetBuffering stdin LineBuffering >> do
  args <- getArgs
  void $ runWithPrelude (parse args)

data Mode = Interactive (Maybe FilePath)
          | Interpret FilePath

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

parseOpts :: [String] -> Praxis Mode
parseOpts args = do
  args <- parseHelp args
  args <- parseDebug args
  (args, interactive) <- parseInteractive args
  (args, file) <- parseFilename args
  when (not (null args)) $ throw Initial (pretty "unknown option: " <> pretty (unwords args))
  if interactive
    then return (Interactive file)
    else case file of
      Just file -> return (Interpret file)
      Nothing   -> throw Initial (pretty "missing file")

parse :: [String] -> Praxis ()
parse xs = do
  mode <- parseOpts xs
  case mode of
    Interactive file -> do
      case file of
        Just file -> do
          text <- liftIO (readFile file)
          eval ProgramT text
          repl
        Nothing   -> repl
    Interpret file -> do
      text <- liftIO (readFile file)
      eval ProgramT text
      runMain

help :: Praxis a
help = Praxis.abort (pretty helpStr) where
  helpStr = "usage: praxis [infile] [OPTION]...\n\n" ++ unlines helpOpts
  helpOpts =
    [ "-d debug"
    , "-i interactive"
    , "-h help"
    ]

forever :: Praxis a -> Praxis a
forever p = try p >> forever p

repl :: Praxis ()
repl = forever $ do
  liftIO (putStr "> " >> hFlush stdout)
  liftIO getLine >>= evalAndPrint

evalAndPrint :: String -> Praxis ()
evalAndPrint s = do
  -- TODO fix this so we can have declarations
  v <- eval ExpT s
  liftIO $ print v
