{-# LANGUAGE QuasiQuotes #-}

module PolySpec where

import           Test.Hspec
import           Text.RawString.QQ

import           Util


spec :: Spec
spec = do

  describe "polymorphic function (swap)" $ do

    let program = [r|
swap : forall a b. (a, b) -> (b, a)
swap (a, b) = (b, a)
|]

    it "parses" $ parse program `shouldReturn` trim [r|
swap_0 : forall a_0 b_0 . ( a_0 , b_0 ) -> ( b_0 , a_0 ) = \ ( a_0 , b_0 ) -> ( b_0 , a_0 )
|]

    it "type checks" $ check program `shouldReturn` trim [r|
swap_0 : forall a_0 b_0 . ( a_0 , b_0 ) -> ( b_0 , a_0 ) = \ ( [a_0] a_0 , [b_0] b_0 ) -> ( [b_0] b_0 , [a_0] a_0 )
|]

    it "evaluates" $ do
      interpret program "swap (0, 1)"      `shouldReturn` "(1, 0)"
      interpret program "swap (True, 1)"   `shouldReturn` "(1, True)"
      interpret program "swap (1, 2, 3)"   `shouldReturn` "((2, 3), 1)"
      interpret program "swap ((2, 3), 1)" `shouldReturn` "(1, (2, 3))"
      interpret program "swap (\"abc\", 0)" `shouldReturn` "(0, \"abc\")"

    it "translates" $ translate program `shouldReturn` trim [r|
/* 2:1 */
auto swap_0 = []<typename a_0, typename b_0>(){
  return std::function([&](std::pair<a_0, b_0> _temp_0){
    auto _temp_1 = praxis::first(_temp_0);
    auto _temp_2 = praxis::second(_temp_0);
    auto a_0 = std::move(_temp_1);
    auto b_0 = std::move(_temp_2);
    return std::make_pair(std::move(b_0), std::move(a_0));
    throw praxis::BindFail("3:6");
  });
};
|]



  describe "polymorphic function with constraint (copy)" $ do

    let program = [r|
copy : forall a | Copy a. a -> (a, a)
copy x = (x, x)
|]

    it "parses" $ parse program `shouldReturn` trim [r|
copy_0 : forall a_0 | Copy a_0 . a_0 -> ( a_0 , a_0 ) = \ x_0 -> ( x_0 , x_0 )
|]

    it "type checks" $ check program `shouldReturn` trim [r|
copy_0 : forall a_0 | Copy a_0 . a_0 -> ( a_0 , a_0 ) = \ [a_0] x_0 -> ( [a_0] x_0 , [a_0] x_0 )
|]

    it "evaluates" $ do
      interpret program "copy 0"         `shouldReturn` "(0, 0)"
      interpret program "copy (0, True)" `shouldReturn` "((0, True), (0, True))"
