{-# LANGUAGE QuasiQuotes #-}

module PolySpec where

import           Test.Hspec
import           Text.RawString.QQ

import           Introspect
import           Util


spec :: Spec
spec = do

  describe "polymorphic function (swap)" $ do

    let program = [r|
swap : forall a b. (a, b) -> (b, a)
swap (a, b) = (b, a)
|]

    it "parses" $ runPretty (parse IProgram program) `shouldReturn` trim [r|
swap_0 : forall a_0 b_0 . ( a_0 , b_0 ) -> ( b_0 , a_0 ) = \ ( a_0 , b_0 ) -> ( b_0 , a_0 )
|]

    it "type checks" $ runPretty (check IProgram program) `shouldReturn` trim [r|
swap_0 : forall a_0 b_0 . ( a_0 , b_0 ) -> ( b_0 , a_0 ) = \ ( [a_0] a_0 , [b_0] b_0 ) -> ( [b_0] b_0 , [a_0] a_0 )
|]

    it "evals" $ do
      runEvaluate program "swap (0, 1)"      `shouldReturn` "(1, 0)"
      runEvaluate program "swap (True, 1)"   `shouldReturn` "(1, True)"
      runEvaluate program "swap (1, 2, 3)"   `shouldReturn` "((2, 3), 1)"
      runEvaluate program "swap ((2, 3), 1)" `shouldReturn` "(1, (2, 3))"
      runEvaluate program "swap (\"abc\", 0)" `shouldReturn` "(0, \"abc\")"


  describe "polymorphic function with constraint (copy)" $ do

    let program = [r|
copy : forall a | Copy a. a -> (a, a)
copy x = (x, x)
|]

    it "parses" $ runPretty (parse IProgram program) `shouldReturn` trim [r|
copy_0 : forall a_0 | Copy a_0 . a_0 -> ( a_0 , a_0 ) = \ x_0 -> ( x_0 , x_0 )
|]

    it "type checks" $ runPretty (check IProgram program) `shouldReturn` trim [r|
copy_0 : forall a_0 | Copy a_0 . a_0 -> ( a_0 , a_0 ) = \ [a_0] x_0 -> ( [a_0] x_0 , [a_0] x_0 )
|]

    it "evals" $ do
      runEvaluate program "copy 0"         `shouldReturn` "(0, 0)"
      runEvaluate program "copy (0, True)" `shouldReturn` "((0, True), (0, True))"
