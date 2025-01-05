{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators       #-}

module Util
  ( parse
  , check
  , evalProgram
  , evalExp

  , runPretty
  , runEvaluate

  , trim
  ) where

import qualified Check
import           Common
import qualified Eval
import           Eval.Value
import           Inbuilts
import           Introspect
import qualified Parse
import           Praxis
import           Print
import           Term


parse :: forall a. Term a => I a -> String -> Praxis (Annotated a)
parse _ term = Parse.parse term :: Praxis (Annotated a)

check :: forall a. Term a => I a -> String -> Praxis (Annotated a)
check _ term = Parse.parse term >>= Check.check :: Praxis (Annotated a)

evalProgram :: String -> Praxis ()
evalProgram program = check IProgram program >>= Eval.run

evalExp :: String -> Praxis Value
evalExp exp = check IExp exp >>= Eval.run


-- Helpers for tests

runPretty :: (Term a, x ~ Annotation a) => Praxis (Annotated a) -> IO String
runPretty = runWith (\x -> fold (runPrintable (pretty x) Types))

runEvaluate :: String -> String -> IO String
runEvaluate program exp = runWith show (evalProgram program >> evalExp exp)

runWith :: (a -> String) -> Praxis a -> IO String
runWith show p = do
  result <- runWithPrelude (flags . silent .= True >> p)
  case result of
    Left error   -> return error
    Right result -> return (show result)

trim :: String -> String
trim = rtrim . ltrim where
  ltrim s = case s of
    ('\n':s) -> ltrim s
    s        -> s
  rtrim = reverse . ltrim . reverse
