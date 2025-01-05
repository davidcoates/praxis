{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators       #-}

module Util
  ( parse
  , check
  , eval

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
parse _ term = Parse.run term :: Praxis (Annotated a)

check :: forall a. Term a => I a -> String -> Praxis (Annotated a)
check ty term = parse ty term >>= Check.run

eval :: forall a. Term a => I a -> String -> Praxis (Eval.Evaluation a)
eval ty term = check ty term >>= Eval.run

-- Helpers for tests

runPretty :: (Term a, x ~ Annotation a) => Praxis (Annotated a) -> IO String
runPretty = runWith (\x -> fold (runPrintable (pretty x) Types))

runEvaluate :: String -> String -> IO String
runEvaluate program exp = runWith show (eval IProgram program >> eval IExp exp)

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
