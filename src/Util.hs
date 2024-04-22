{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators       #-}

module Util where

import qualified Check      (check)
import           Common
import           Executors
import           Inbuilts
import           Introspect
import qualified Parse      (parse)
import           Praxis
import           Print
import           Term


runShow :: Show a => Praxis a -> IO String
runShow = runWith show

runPretty :: (Term a, x ~ Annotation a) => Praxis (Annotated a) -> IO String
runPretty = runWith (\x -> fold (runPrintable (pretty x) Types))

runWith :: (a -> String) -> Praxis a -> IO String
runWith show p = do
  result <- runSilent initialState p
  case result of
    Left error   -> return error
    Right result -> return (show result)

check :: String -> IO String
check program = runPretty (Parse.parse program >>= Check.check :: Praxis (Annotated Program))

parse :: String -> IO String
parse program = runPretty (Parse.parse program :: Praxis (Annotated Program))

parseAs :: forall a. Term a => I a -> String -> IO String
parseAs _ term = runPretty (Parse.parse term :: Praxis (Annotated a))

-- Helper for interperting a program followed by an expression and printing the resulting value
interpret :: String -> String -> IO String
interpret program exp = runShow $ do
  interpretProgram program
  interpretExp exp

translate :: String -> IO String
translate program = runWith id (translateProgram program)

trim :: String -> String
trim = rtrim . ltrim where
  ltrim s = case s of
    ('\n':s) -> ltrim s
    s        -> s
  rtrim = reverse . ltrim . reverse

compile :: String -> IO Bool
compile program = do
  (result, _) <- runPraxis (compileProgram program Nothing) initialState
  case result of
    Left error   -> return False
    Right result -> return True

compileAndRun :: String -> String -> IO String
compileAndRun program exp  = do
  let program' = program ++ "\n" ++ "main : () -> ()\n" ++ "main () = print (" ++ exp ++ ")"
  (result, _) <- runPraxis (compileAndRunProgram program') initialState
  case result of
    Left error   -> return error
    Right result -> return (trim result)
