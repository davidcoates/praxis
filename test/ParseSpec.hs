module ParseSpec where

import           Parse         (parse)
import           Praxis
import           Term

import           Control.Monad (forM_)
import           Prelude       hiding (exp)
import           Test.Hspec

matches a b = (a, b)

exps =
  [ "1 + 2 + 3" `matches` "(1 + 2) + 3"
  , "1 + 2 * 3" `matches` "1 + (2 * 3)"
  , "f x 1 + g y * z" `matches` "((f x) 1) + ((g y) * z)"
  , "f x + f y + f z" `matches` "((f x) + (f y)) + (f z)" ]

tys =
  [ "Int -> Int -> Int" `matches` "Int -> (Int -> Int)"
  , "A B C" `matches` "(A B) C"
  , "Maybe (Maybe a) -> Maybe b" `matches` "(Maybe (Maybe a)) -> (Maybe b)"
  ]

programs =
  [ " fac : Int -> Int   \n\
    \ fac = cases        \n\
    \ 0 -> 1             \n\
    \ n -> n * fac (n -1)"
    `matches` "{ fac : Int -> Int; fac = cases { 0 -> 1; n -> n * (fac (n - 1)) } }"
  ]

exp :: String -> Simple Exp
exp s = runInternal emptyState (parse s)

ty :: String -> Simple Type
ty s = runInternal emptyState (parse s)

program :: String -> Simple Program
program s = runInternal emptyState (parse s)

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
