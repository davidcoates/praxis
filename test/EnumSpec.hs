{-# LANGUAGE QuasiQuotes #-}

module EnumSpec where

import           Test.Hspec
import           Text.RawString.QQ

import           Util


spec :: Spec
spec = describe "enum Color" $ do

  let program = [r|
enum Color = Red | Green | Blue

color_to_char color = case color of
  Red   -> 'R'
  Green -> 'G'
  Blue  -> 'B'
|]

  it "parses" $ parse program `shouldReturn` trim [r|
enum Color = Red | Green | Blue
color_to_char_0 = \ color_0 -> case color_0 of
  Red -> 'R'
  Green -> 'G'
  Blue -> 'B'
|]

  it "type checks" $ check program `shouldReturn` trim [r|
enum Color = Red | Green | Blue
color_to_char_0 = \ [Color] color_0 -> [Char] case [Color] color_0 of
  [Color] Red -> [Char] 'R'
  [Color] Green -> [Char] 'G'
  [Color] Blue -> [Char] 'B'
|]

  it "evaluates" $ do
    interpret program "color_to_char Blue" `shouldReturn` "'B'"

  it "translates" $ translate program `shouldReturn` trim [r|
enum Color {
  _conRed, _conGreen, _conBlue
};
/* 4:1 */
auto color_to_char_0 = std::function([](Color _temp_0){
  auto color_0 = std::move(_temp_0);
  return [&](){
    auto _temp_1 = std::move(color_0);
    if (_temp_1 == _conRed) {
      return 'R';
    }
    if (_temp_1 == _conGreen) {
      return 'G';
    }
    if (_temp_1 == _conBlue) {
      return 'B';
    }
    throw praxis::CaseFail("4:23");
  }();
  throw praxis::BindFail("4:15");
});
|]

  it "compiles" $ compile program `shouldReturn` True

  it "runs" $ do
    compileAndRun program "color_to_char Blue" `shouldReturn` "B"


