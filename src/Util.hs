{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators       #-}

module Util
  ( check
  , check'
  , parse
  , parseAs
  , translate
  , evaluate

  , trim
  ) where

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

-- TODO make these names consistent
check' :: String -> String -> IO String
check' program exp = runPretty $ do
  (Parse.parse program >>= Check.check) :: Praxis (Annotated Program)
  (Parse.parse exp >>= Check.check) :: Praxis (Annotated Exp)

parse :: String -> IO String
parse program = runPretty (Parse.parse program :: Praxis (Annotated Program))

parseAs :: forall a. Term a => I a -> String -> IO String
parseAs _ term = runPretty (Parse.parse term :: Praxis (Annotated a))

-- Helper for interperting a program followed by an expression and printing the resulting value
evaluate :: String -> String -> IO String
evaluate program exp = runShow $ do
  evaluateProgram program
  evaluateExp exp

translate :: String -> IO String
translate program = runWith id (translateProgram program)

trim :: String -> String
trim = rtrim . ltrim where
  ltrim s = case s of
    ('\n':s) -> ltrim s
    s        -> s
  rtrim = reverse . ltrim . reverse
