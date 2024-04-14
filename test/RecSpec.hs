{-# LANGUAGE QuasiQuotes #-}

module RecSpec where

import           Test.Hspec
import           Text.RawString.QQ

import           Util


spec :: Spec
spec = do

  describe "recursion (fac)" $ do

    let program = [r|
rec
  fac = cases
    0 -> 1
    n -> n * fac (n - 1)
|]

    it "parses" $ parse program `shouldReturn` trim [r|
rec
  fac_0 = cases
    0 -> 1
    n_0 -> multiply_int ( n_0 , fac_0 subtract_int ( n_0 , 1 ) )
|]

    it "type checks" $ check program `shouldReturn` trim [r|
rec
  fac_0 = [Int -> Int] cases
    [Int] 0 -> [Int] 1
    [Int] n_0 -> [( Int , Int ) -> Int] multiply_int ( [Int] n_0 , [Int -> Int] fac_0 [( Int , Int ) -> Int] subtract_int ( [Int] n_0 , [Int] 1 ) )
|]

    it "evaluates" $ do
      interpret program "fac 0"  `shouldReturn` "1"
      interpret program "fac 5"  `shouldReturn` "120"
      interpret program "fac 15" `shouldReturn` "1307674368000"

    it "translates" $ translate program `shouldReturn` trim [r|
auto temp_0_ = [](auto temp_1_) -> std::tuple<std::function<int(int)>> {
  return std::tuple{
    /* 2:1 */
    std::function([&](int temp_2_){
      auto [fac_0] = temp_1_(temp_1_);
      if (temp_2_ == 0) {
        return 1;
      }
      auto n_0 = std::move(temp_2_);
      return std::move(multiply_int)(std::make_pair(std::move(n_0), std::move(fac_0)(std::move(subtract_int)(std::make_pair(std::move(n_0), 1)))));
      throw praxis::CaseFail("3:9");
    })
  };
};
auto [fac_0] = temp_0_(temp_0_);
|]

    it "compiles" $ compile program `shouldReturn` True

    it "runs" $ do
      compileAndRun program "fac 0"  `shouldReturn` "1"
      compileAndRun program "fac 5"  `shouldReturn` "120"
      compileAndRun program "fac 15" `shouldReturn` "2004310016" -- overflow moment (TODO should use fixed width)



  describe "mutual recursion (is_even / is_odd)" $ do

    let program = [r|
rec
  is_even = cases
    0 -> True
    n -> is_odd (n - 1)

  is_odd = cases
    0 -> False
    n -> is_even (n - 1)
|]

    it "parses" $ parse program `shouldReturn` trim [r|
rec
  is_even_0 = cases
    0 -> True
    n_0 -> is_odd_0 subtract_int ( n_0 , 1 )
  is_odd_0 = cases
    0 -> False
    n_1 -> is_even_0 subtract_int ( n_1 , 1 )
|]

    it "type checks" $ check program `shouldReturn` trim [r|
rec
  is_even_0 = [Int -> Bool] cases
    [Int] 0 -> [Bool] True
    [Int] n_0 -> [Int -> Bool] is_odd_0 [( Int , Int ) -> Int] subtract_int ( [Int] n_0 , [Int] 1 )
  is_odd_0 = [Int -> Bool] cases
    [Int] 0 -> [Bool] False
    [Int] n_1 -> [Int -> Bool] is_even_0 [( Int , Int ) -> Int] subtract_int ( [Int] n_1 , [Int] 1 )
|]

    it "translates" $ translate program `shouldReturn` trim [r|
auto temp_0_ = [](auto temp_1_) -> std::tuple<std::function<bool(int)>, std::function<bool(int)>> {
  return std::tuple{
    /* 2:1 */
    std::function([&](int temp_2_){
      auto [is_even_0, is_odd_0] = temp_1_(temp_1_);
      if (temp_2_ == 0) {
        return true;
      }
      auto n_0 = std::move(temp_2_);
      return std::move(is_odd_0)(std::move(subtract_int)(std::make_pair(std::move(n_0), 1)));
      throw praxis::CaseFail("3:13");
    }),
    /* 2:1 */
    std::function([&](int temp_3_){
      auto [is_even_0, is_odd_0] = temp_1_(temp_1_);
      if (temp_3_ == 0) {
        return false;
      }
      auto n_1 = std::move(temp_3_);
      return std::move(is_even_0)(std::move(subtract_int)(std::make_pair(std::move(n_1), 1)));
      throw praxis::CaseFail("7:12");
    })
  };
};
auto [is_even_0, is_odd_0] = temp_0_(temp_0_);
|]

    it "compiles" $ compile program `shouldReturn` True

    it "evaluates" $ do
      interpret program "is_even 0" `shouldReturn` "True"
      interpret program "is_even 1" `shouldReturn` "False"
      interpret program "is_even 2" `shouldReturn` "True"
      interpret program "is_even 3" `shouldReturn` "False"
      interpret program "is_odd 0" `shouldReturn` "False"
      interpret program "is_odd 1" `shouldReturn` "True"
      interpret program "is_odd 2" `shouldReturn` "False"
      interpret program "is_odd 3" `shouldReturn` "True"
