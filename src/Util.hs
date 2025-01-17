{-# LANGUAGE DataKinds #-}

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
import qualified Monomorphize
import           Praxis
import           Print
import           Stage
import           Term


parse :: forall a. IsTerm a => TermT a -> String -> Praxis (Annotated Parse a)
parse _ term = Parse.run term :: Praxis (Annotated Parse a)

check :: forall a. IsTerm a => TermT a -> String -> Praxis (Annotated TypeCheck a)
check ty term = parse ty term >>= Check.run

{-
-- FIXME
monomorphize :: forall a. IsTerm a => TermT a -> String -> Praxis (Monomorphize.Monomorphization a)
monomorphize ty term = check ty term >>= Monomorphize.run
-}

eval :: forall a. IsTerm a => TermT a -> String -> Praxis (Eval.Evaluation a)
eval ty term = check ty term >>= Eval.run

-- Helpers for tests

runPretty :: (IsTerm a, IsStage s) => Praxis (Annotated s a) -> IO String
runPretty = runWith (\x -> fold (pretty x))

runEvaluate :: String -> String -> IO String
runEvaluate program exp = runWith show (eval ProgramT program >> eval ExpT exp)

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
