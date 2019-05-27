module ParseSpec where

import           Annotate      (Parsed)
import           AST
import           Parse         (parse)
import           Praxis
import           Type

import           Control.Monad (forM_)
import           Prelude       hiding (exp)
import           Test.Hspec

matches a b = (a, b)

exps =
  [ "1 + 2 + 3" `matches` "(1 + 2) + 3"
  , "1 + 2 * 3" `matches` "1 + (2 * 3)"
  , "f x 1 + g y * z" `matches` "((f x) 1) + ((g y) * z)"
  , "f x + f y + f z" `matches` "((f x) + (f y)) + (f z)" ]

programs =
  [
  ]

tys =
  [ "Int -> Int -> Int" `matches` "Int -> (Int -> Int)"
  ]

exp :: String -> Parsed Exp
exp s = runInternal emptyState (parse s)

program :: String -> Parsed Program
program s = runInternal emptyState (parse s)

ty :: String -> Parsed Type
ty s = runInternal emptyState (parse s)

spec :: Spec
spec = do
  describe "Expressions" $ do
    forM_ exps $ \(a, b) -> do
      it (a ++ " should parse as " ++ b) $ do
        exp a `shouldBe` exp b
  describe "Types" $ do
    forM_ tys $ \(a, b) -> do
      it (a ++ " should parse as " ++ b) $ do
        ty a `shouldBe` ty b
  describe "Programs" $ do
    forM_ programs $ \(a, b) -> do
      it (a ++ " should parse as " ++ b) $ do
        program a `shouldBe` program b
