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

  it "translates" $ translate program `shouldReturn` trim [r|
TODO
|]

  it "evaluates" $ do
    evaluate program "color_to_char Blue" `shouldReturn` "'B'"
