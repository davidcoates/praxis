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
import qualified Translate  (prelude)

instance (Term a, x ~ Annotation a) => Show (Tag (Source, Maybe x) a) where
  show x = fold (runPrintable (pretty x) Types)

run :: Show a => Praxis a -> IO String
run = runWith show

runWith :: (a -> String) -> Praxis a -> IO String
runWith show p = do
  result <- runSilent initialState p
  case result of
    Left error   -> return error
    Right result -> return (show result)

check :: String -> IO String
check program = run (Parse.parse program >>= Check.check :: Praxis (Annotated Program))

parse :: String -> IO String
parse program = run (Parse.parse program :: Praxis (Annotated Program))

parseAs :: forall a. Term a => I a -> String -> IO String
parseAs _ term = run (Parse.parse term :: Praxis (Annotated a))

-- Helper for interperting a program followed by an expression and printing the resulting value
interpret :: String -> String -> IO String
interpret program exp = run $ do
    interpretProgram program
    interpretExp exp

translate :: String -> IO String
translate program = runWith id (translateProgram program)

trim :: String -> String
trim = init . tail

compile :: String -> IO Bool
compile program = do
  (result, _) <- runPraxis (compileProgram program Nothing) initialState
  case result of
    Left error   -> return False
    Right result -> return True
