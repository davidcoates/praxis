{-# LANGUAGE QuasiQuotes #-}

module ExpSpec where

import           Test.Hspec
import           Text.RawString.QQ

import           Util


spec :: Spec
spec = do

  describe "do" $ do

    let program = [r|
foo = do
  let x = 1
  ()
  let y = 2
  x + y
|]

    it "parses" $ parse program `shouldReturn` trim [r|
foo_0 = let x_0 = 1 in ( ) seq let y_0 = 2 in add_int ( x_0 , y_0 )
|]

    it "type checks" $ check program `shouldReturn` trim [r|
foo_0 = [Int] let [Int] x_0 = [Int] 1 in [Int] [( )] ( ) seq [Int] let [Int] y_0 = [Int] 2 in [( Int , Int ) -> Int] add_int ( [Int] x_0 , [Int] y_0 )
|]

    it "translates" $ translate program `shouldReturn` trim [r|
/* 2:1 */
auto foo_0 = [](){
  auto _temp_0 = 1;
  auto x_0 = std::move(_temp_0);
  return (std::monostate{}, [&](){
    auto _temp_1 = 2;
    auto y_0 = std::move(_temp_1);
    return std::move(add_int)(std::make_pair(std::move(x_0), std::move(y_0)));
    throw praxis::BindFail("5:7");
  }());
  throw praxis::BindFail("3:7");
}();
|]

    it "compiles" $ compile program `shouldReturn` True

    it "runs" $ compileAndRun program "foo" `shouldReturn` "3"



  describe "tuple" $ do

    let program = "x = (1, True, \"abc\")"
    it "parses" $ parse program `shouldReturn` trim [r|
x_0 = ( 1 , True , "abc" )
|]

    it "type checks" $ check program `shouldReturn` trim [r|
x_0 = ( [Int] 1 , [Bool] True , [& 'l0 String] "abc" )
|]

    it "translates" $ translate program `shouldReturn` trim [r|
/* 1:1 */
auto x_0 = std::make_pair(1, std::make_pair(true, "abc"));
|]

    it "compiles" $ compile program `shouldReturn` True



  describe "if then else (min)" $ do

    let program = "min (x, y) = if x < y then x else y"

    it "parses" $ parse program `shouldReturn` trim [r|
min_0 = \ ( x_0 , y_0 ) -> if lt_int ( x_0 , y_0 ) then x_0 else y_0
|]

    it "type checks" $ check program `shouldReturn` trim [r|
min_0 = \ ( [Int] x_0 , [Int] y_0 ) -> [Int] if [( Int , Int ) -> Bool] lt_int ( [Int] x_0 , [Int] y_0 ) then [Int] x_0 else [Int] y_0
|]

    it "evaluates" $ do
      interpret program "min (1, 2)" `shouldReturn` "1"
      interpret program "min (2, 1)" `shouldReturn` "1"
      interpret program "min (1, 1)" `shouldReturn` "1"

    it "translates" $ translate program `shouldReturn` trim [r|
/* 1:1 */
auto min_0 = std::function([](std::pair<int, int> _temp_0){
  auto _temp_1 = praxis::first(_temp_0);
  auto _temp_2 = praxis::second(_temp_0);
  auto x_0 = std::move(_temp_1);
  auto y_0 = std::move(_temp_2);
  return (std::move(lt_int)(std::make_pair(std::move(x_0), std::move(y_0)))) ? (std::move(x_0)) : (std::move(y_0));
  throw praxis::BindFail("1:5");
});
|]

    it "compiles" $ compile program `shouldReturn` True

    it "runs" $ do
      compileAndRun program "min (1, 2)" `shouldReturn` "1"
      compileAndRun program "min (2, 1)" `shouldReturn` "1"
      compileAndRun program "min (1, 1)" `shouldReturn` "1"



  describe "switch (sign)" $ do

    let program = [r|
sign : Int -> Int
sign n = switch
  n  < 0 -> -1
  n == 0 ->  0
  n  > 0 -> +1
|]

    it "parses" $ parse program `shouldReturn` trim [r|
sign_0 : Int -> Int = \ n_0 -> switch
  lt_int ( n_0 , 0 ) -> negate_int 1
  eq_int ( n_0 , 0 ) -> 0
  gt_int ( n_0 , 0 ) -> unary_plus_int 1
|]

    it "type checks" $ check program `shouldReturn` trim [r|
sign_0 : Int -> Int = \ [Int] n_0 -> [Int] switch
  [( Int , Int ) -> Bool] lt_int ( [Int] n_0 , [Int] 0 ) -> [Int -> Int] negate_int [Int] 1
  [( Int , Int ) -> Bool] eq_int ( [Int] n_0 , [Int] 0 ) -> [Int] 0
  [( Int , Int ) -> Bool] gt_int ( [Int] n_0 , [Int] 0 ) -> [Int -> Int] unary_plus_int [Int] 1
|]

    it "evaluates" $ do
      interpret program "sign 0"    `shouldReturn` "0"
      interpret program "sign 10"   `shouldReturn` "1"
      interpret program "sign (-5)" `shouldReturn` "-1"
      interpret program "sign -5"   `shouldReturn` trim [r|
type check error: unable to satisfy: Int = Int -> Int
  | derived from: ( Int , Int ) -> Int = ( Int -> Int , Int ) -> ^t6
  | primary cause: application [( Int , Int ) -> Int] subtract_int ($) ( [Int -> Int] sign_0 , [Int] 5 ) at 1:1
|]  -- Note: Parses as "sign - 5" (binary subtract)

    it "translates" $ translate program `shouldReturn` trim [r|
/* 2:1 */
auto sign_0 = std::function([](int _temp_0){
  auto n_0 = std::move(_temp_0);
  return [&](){
    if (std::move(lt_int)(std::make_pair(std::move(n_0), 0))) {
      return std::move(negate_int)(1);
    }
    if (std::move(eq_int)(std::make_pair(std::move(n_0), 0))) {
      return 0;
    }
    if (std::move(gt_int)(std::make_pair(std::move(n_0), 0))) {
      return std::move(unary_plus_int)(1);
    }
    throw praxis::SwitchFail("3:10");
  }();
  throw praxis::BindFail("3:6");
});
|]

    it "compiles" $ compile program `shouldReturn` True

    it "runs" $ do
      compileAndRun program "sign 0"    `shouldReturn` "0"
      compileAndRun program "sign 10"   `shouldReturn` "1"
      compileAndRun program "sign (-5)" `shouldReturn` "-1"
