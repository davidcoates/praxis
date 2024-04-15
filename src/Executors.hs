module Executors
  ( interpretExp
  , interpretProgram
  , translateProgram
  , compileProgram
  , compileAndRunProgram
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
translateProgram = translateProgram' Translate.NoPrelude

translateProgram' :: Translate.Mode -> String -> Praxis String
translateProgram' mode program = do
  program <- parse program >>= check :: Praxis (Annotated Program)
  translation <- Translate.runProgram mode program
  return translation

compileProgram :: String -> Maybe FilePath -> Praxis ()
compileProgram program outFile = do
  let mode = case outFile of { Just _ -> Translate.PreludeWithMain; Nothing -> Translate.Prelude }
  program <- translateProgram' mode program
  withSystemTempDirectory "praxis" (compile program)
  where
    compile :: String -> FilePath -> Praxis ()
    compile program dir = do
      let sourceFile = dir ++ "/praxis.cc"
      liftIO $ writeFile sourceFile program
      let
        cmds = case outFile of
          Just outFile -> [ sourceFile, "-o", outFile ]
          Nothing      -> [ "-c", sourceFile, "-o", "/dev/null" ]
      (exitCode, _, errLog) <- liftIO $ readProcessWithExitCode "g++" cmds ""
      case exitCode of
        ExitSuccess -> return ()
        _           -> throw errLog

compileAndRunProgram :: String -> Praxis String
compileAndRunProgram program = do
  program <- translateProgram' Translate.PreludeWithMain program
  withSystemTempDirectory "praxis" (compileAndRun program)
  where
    compileAndRun :: String -> FilePath -> Praxis String
    compileAndRun program dir = do
      let sourceFile = dir ++ "/praxis.cc"
      let outFile = dir ++ "/praxis.bin"
      liftIO $ writeFile sourceFile program
      (exitCode, _, errLog) <- liftIO $ readProcessWithExitCode "g++" [ sourceFile, "-o", outFile ] ""
      case exitCode of
        ExitSuccess -> do
          (exitCode, outLog, errLog) <- liftIO $ readProcessWithExitCode outFile [] ""
          case exitCode of
            ExitSuccess -> return outLog
            _           -> throw errLog
        _           -> throw errLog
