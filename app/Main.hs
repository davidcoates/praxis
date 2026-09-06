module Main where

import qualified Codegen
import           Common
import           Eval               (runMain)
import           Inbuilts           (runWithPrelude)
import           Introspect
import           Praxis
import           Stage
import           Term
import           Util               (eval, lower)

import           Control.Monad      (void, when)
import           Data.List          (delete)
import           System.Environment
import           System.Exit        (exitFailure)
import           System.FilePath    (dropExtension, hasExtension)
import           System.IO


main :: IO ()
main = hSetBuffering stdin LineBuffering >> do
  args <- getArgs
  result <- runWithPrelude (parse args)
  case result of
    Left err -> hPutStrLn stderr err >> exitFailure
    Right () -> return ()

data Mode = Interactive (Maybe FilePath)
          | Interpret FilePath
          | Compile FilePath FilePath Bool
          -- ^ Input, output, and whether to stop after writing the LLVM IR

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

parseCompile :: [String] -> Praxis ([String], Bool, Bool)
parseCompile args = return (delete "--emit-llvm" (delete "-c" args), "-c" `elem` args, "--emit-llvm" `elem` args)

parseOutput :: [String] -> Praxis ([String], Maybe FilePath)
parseOutput args = case break (== "-o") args of
  (before, "-o" : out : after) -> return (before ++ after, Just out)
  (_, ["-o"])                  -> throw Initial ("missing argument to -o" :: String)
  _                            -> return (args, Nothing)

parseOpts :: [String] -> Praxis Mode
parseOpts args = do
  args <- parseHelp args
  args <- parseDebug args
  (args, interactive) <- parseInteractive args
  (args, compile, emitLLVM) <- parseCompile args
  (args, output) <- parseOutput args
  (args, file) <- parseFilename args
  when (not (null args)) $ throw Initial (pretty "unknown option: " <> pretty (unwords args))
  if interactive
    then return (Interactive file)
    else case file of
      Just file
        | compile || emitLLVM -> do
            let out = case output of
                  Just out -> out
                  Nothing  -> if hasExtension file then dropExtension file else file ++ ".out"
            return (Compile file out emitLLVM)
        | otherwise -> return (Interpret file)
      Nothing -> throw Initial (pretty "missing file")

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
    Compile file out emitLLVM -> do
      text <- liftIO (readFile file)
      program <- lower ProgramT text
      m <- Codegen.run program
      Codegen.compile m out emitLLVM

help :: Praxis a
help = Praxis.abort (pretty helpStr) where
  helpStr = "usage: praxis [infile] [OPTION]...\n\n" ++ unlines helpOpts
  helpOpts =
    [ "-c           compile to an executable (with clang)"
    , "--emit-llvm  write the LLVM IR only"
    , "-o <file>    the output of -c (default: the input without its extension)"
    , "-d           debug"
    , "-i           interactive"
    , "-h           help"
    ]

forever :: Praxis a -> Praxis a
forever p = do
  result <- try p
  case result of
    Left err -> liftIO (hPutStrLn stderr err)
    Right _  -> return ()
  forever p

repl :: Praxis ()
repl = forever $ do
  liftIO (putStr "> " >> hFlush stdout)
  liftIO getLine >>= evalAndPrint

evalAndPrint :: String -> Praxis ()
evalAndPrint s = do
  -- TODO fix this so we can have declarations
  v <- eval ExpT s
  liftIO $ print v
