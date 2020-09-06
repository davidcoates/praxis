module ParseSpec where

import           Common
import           Inbuilts
import           Introspect
import           Parse         (parse)
import           Praxis
import           Term

import           Control.Monad (forM_)
import           Prelude       hiding (exp)
import           Test.Hspec

matches a b = (a, b)

exps =
  [ "1 + 2" `matches` "1 + 2"
  , "1 + 2 + 3" `matches` "(1 + 2) + 3"
  , "1 + 2 * 3" `matches` "1 + (2 * 3)"
  , "1 - - 2" `matches` "1 - (- 2)"
  , "f x 1 + g y * z" `matches` "(f (x 1)) + ((g y) * z)"
  , "f x + f y + f z" `matches` "((f x) + (f y)) + (f z)" ]

tys =
  [ "Int -> Int -> Int" `matches` "Int -> (Int -> Int)"
  , "A B C" `matches` "A (B C)"
  , "Maybe Maybe a -> Maybe b" `matches` "(Maybe (Maybe a)) -> (Maybe b)"
  ]

-- TODO broken - simply check parsing + unparsing = identity
programs =
  [ unlines
      [ "fac : Int -> Int"
      , "fac = cases"
      , "  0 -> 1"
      , "  n -> n * fac (n -1)"
      ] `matches` "{ fac : Int -> Int; fac = cases { 0 -> 1; n -> n * (fac (n - 1)) } }"
  ]

exp :: String -> Annotated Exp
exp s = runInternal initialState (parse s)

ty :: String -> Annotated Type
ty s = runInternal initialState (parse s)

program :: String -> Annotated Program
program s = runInternal initialState (parse s)

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
