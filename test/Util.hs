{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeOperators     #-}
{-# LANGUAGE GADTs     #-}
{-# LANGUAGE ScopedTypeVariables     #-}

module Util where

import qualified Check             (check)
import           Common
import           Executors
import           Inbuilts
import           Introspect
import qualified Parse             (parse)
import           Praxis
import           Print
import           Term


instance (Term a, x ~ Annotation a) => Show (Tag (Source, Maybe x) a) where
  show x = fold (runPrintable (pretty x) Types)

run :: Show a => Praxis a -> IO String
run p = do
  x <- runSilent initialState p
  case x of
    Left e  -> return e
    Right y -> return (show y)

check :: String -> IO String
check s = run (Parse.parse s >>= Check.check :: Praxis (Annotated Program))

parse :: String -> IO String
parse s = run (Parse.parse s :: Praxis (Annotated Program))

parseAs :: forall a. Term a => I a -> String -> IO String
parseAs _ s = run (Parse.parse s :: Praxis (Annotated a))

-- Helper for interperting a program followed by an expression and printing the resulting value
interpret :: String -> String -> IO String
interpret program exp = run $ do
    interpretProgram program
    interpretExp exp

trim :: String -> String
trim = init . tail

