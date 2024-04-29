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
foo_0 = let x_0 = 1 in ( ) seq let y_0 = 2 in add ( x_0 , y_0 )
|]

    it "type checks" $ check program `shouldReturn` trim [r|
foo_0 = [I32] let [I32] x_0 = [I32] 1 in [I32] [( )] ( ) seq [I32] let [I32] y_0 = [I32] 2 in [( I32 , I32 ) -> I32] add ( [I32] x_0 , [I32] y_0 )
|]

    it "translates" $ translate program `shouldReturn` trim [r|
/* 2:1 */
auto foo_0 = [](){
  auto _temp_0 = static_cast<I32>(1);
  auto x_0 = std::move(_temp_0);
  return (std::monostate{}, [&](){
    auto _temp_1 = static_cast<I32>(2);
    auto y_0 = std::move(_temp_1);
    return std::move(add).template operator()<I32>()(std::make_pair(std::move(x_0), std::move(y_0)));
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
x_0 = ( [I32] 1 , [Bool] True , [& 'l0 String] "abc" )
|]

    it "translates" $ translate program `shouldReturn` trim [r|
/* 1:1 */
auto x_0 = std::make_pair(static_cast<I32>(1), std::make_pair(true, "abc"));
|]

    it "compiles" $ compile program `shouldReturn` True



  describe "if then else (min)" $ do

    let program = "min (x, y) = if x < y then x else y"

    it "parses" $ parse program `shouldReturn` trim [r|
min_0 = \ ( x_0 , y_0 ) -> if lt ( x_0 , y_0 ) then x_0 else y_0
|]

    it "type checks" $ check program `shouldReturn` trim [r|
min_0 = \ ( [I32] x_0 , [I32] y_0 ) -> [I32] if [( I32 , I32 ) -> Bool] lt ( [I32] x_0 , [I32] y_0 ) then [I32] x_0 else [I32] y_0
|]

    it "evaluates" $ do
      interpret program "min (1, 2)" `shouldReturn` "1"
      interpret program "min (2, 1)" `shouldReturn` "1"
      interpret program "min (1, 1)" `shouldReturn` "1"

    it "translates" $ translate program `shouldReturn` trim [r|
/* 1:1 */
auto min_0 = std::function([](std::pair<I32, I32> _temp_0){
  auto _temp_1 = praxis::first(_temp_0);
  auto _temp_2 = praxis::second(_temp_0);
  auto x_0 = std::move(_temp_1);
  auto y_0 = std::move(_temp_2);
  return (std::move(lt).template operator()<I32>()(std::make_pair(std::move(x_0), std::move(y_0)))) ? (std::move(x_0)) : (std::move(y_0));
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
sign : I32 -> I32
sign n = switch
  n  < 0 -> -1
  n == 0 ->  0
  n  > 0 ->  1
|]

    it "parses" $ parse program `shouldReturn` trim [r|
sign_0 : I32 -> I32 = \ n_0 -> switch
  lt ( n_0 , 0 ) -> -1
  eq ( n_0 , 0 ) -> 0
  gt ( n_0 , 0 ) -> 1
|]

    it "type checks" $ check program `shouldReturn` trim [r|
sign_0 : I32 -> I32 = \ [I32] n_0 -> [I32] switch
  [( I32 , I32 ) -> Bool] lt ( [I32] n_0 , [I32] 0 ) -> [I32] -1
  [( I32 , I32 ) -> Bool] eq ( [I32] n_0 , [I32] 0 ) -> [I32] 0
  [( I32 , I32 ) -> Bool] gt ( [I32] n_0 , [I32] 0 ) -> [I32] 1
|]

    it "evaluates" $ do
      interpret program "sign 0"    `shouldReturn` "0"
      interpret program "sign 10"   `shouldReturn` "1"
      interpret program "sign (-5)" `shouldReturn` "-1"
      interpret program "sign -5"   `shouldReturn` "-1"
      interpret program "sign - 5"  `shouldReturn` trim [r|
type check error: unable to satisfy: I32 -> I32 = I32
  | derived from: Integral ( I32 -> I32 )
  | primary cause: integer literal 5 at 1:8
  | secondary cause: application [( I32 -> I32 , I32 -> I32 ) -> I32 -> I32] subtract ($) ( [I32 -> I32] sign_0 , [I32 -> I32] 5 ) at 1:1
|]  -- Note: Parses as "sign - 5" (binary subtract)

    it "translates" $ translate program `shouldReturn` trim [r|
/* 2:1 */
auto sign_0 = std::function([](I32 _temp_0){
  auto n_0 = std::move(_temp_0);
  return [&](){
    if (std::move(lt).template operator()<I32>()(std::make_pair(std::move(n_0), static_cast<I32>(0)))) {
      return static_cast<I32>(-1);
    }
    if (std::move(eq).template operator()<I32>()(std::make_pair(std::move(n_0), static_cast<I32>(0)))) {
      return static_cast<I32>(0);
    }
    if (std::move(gt).template operator()<I32>()(std::make_pair(std::move(n_0), static_cast<I32>(0)))) {
      return static_cast<I32>(1);
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
