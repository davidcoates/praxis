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
import qualified LambdaLift
import qualified Monomorphize
import qualified Parse
import           Praxis
import           Print
import           Stage
import           Term


parse :: forall a. IsTerm a => TermT a -> String -> Praxis (Annotated Parse a)
parse _ term = Parse.run term :: Praxis (Annotated Parse a)

check :: forall a. IsTerm a => TermT a -> String -> Praxis (Annotated TypeCheck a)
check ty term = parse ty term >>= Check.run

eval :: forall a. IsTerm a => TermT a -> String -> Praxis (Eval.Evaluation a)
eval ty term = do
  checked <- check ty term
  mono    <- Monomorphize.run checked
  case (ty, mono) of
    (ProgramT, prog)    -> do
      lifted <- LambdaLift.run prog
      Eval.run lifted
    (ExpT, (prog, exp)) -> do
      prog'          <- LambdaLift.run prog
      (prog'', exp') <- LambdaLift.runExp prog' exp
      Eval.run prog'' >> Eval.run exp'

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
