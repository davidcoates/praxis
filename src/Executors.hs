module Executors
  ( interpretExp
  , interpretProgram
  , translateProgram
  , compileProgram
  ) where

import           Check          (check)
import           Common
import qualified Eval
import           Parse          (parse)
import           Praxis
import           Term
import qualified Translate
import           Value          (Value)

import           System.Exit    (ExitCode (..))
import           System.IO
import           System.IO.Temp
import           System.Process

interpretExp :: String -> Praxis Value
interpretExp exp = do
  exp <- parse exp >>= check :: Praxis (Annotated Exp)
  value <- Eval.runExp exp
  return value

interpretProgram :: String -> Praxis (Annotated Program)
interpretProgram program = do
  program <- parse program >>= check :: Praxis (Annotated Program)
  () <- Eval.runProgram program
  return program

translateProgram :: String -> Praxis String
translateProgram program = do
  program <- parse program >>= check :: Praxis (Annotated Program)
  translation <- Translate.runProgram program
  return translation

coerceMain :: Praxis String
coerceMain = do
  requireMain
  return $ "\nint main(){ main_0(praxis::Unit{}); }"

compileProgram :: String -> Maybe FilePath -> Praxis ()
compileProgram program outFile = do
  program <- translateProgram program
  postlude <- case outFile of { Just _ -> coerceMain; Nothing -> return ""; } -- If we are linking, then main needs to be defined.
  errLog <- liftIO $ withSystemTempFile "praxis.cc" (compile (Translate.prelude ++ program ++ postlude))
  case errLog of
    Just errLog -> throw errLog
    Nothing     -> return ()
  where
    compile :: String -> FilePath -> Handle -> IO (Maybe String)
    compile program filepath handle = do
      hPutStr handle program
      hFlush handle
      let
        cmds = case outFile of
          Just outFile -> [ filepath, "-o", outFile ]
          Nothing      -> [ "-c", filepath, "-o", "/dev/null" ]
      (errCode, _, errLog) <- readProcessWithExitCode "g++" cmds ""
      case errCode of
        ExitSuccess -> return Nothing
        _           -> return (Just errLog)

-- compileAndRunProgram :: String -> Praxis String
