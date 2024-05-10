{-# LANGUAGE QuasiQuotes #-}

module EnumSpec where

import           Test.Hspec
import           Text.RawString.QQ

import           Introspect
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

  it "parses" $ runPretty (parse IProgram program) `shouldReturn` trim [r|
enum Color = Red | Green | Blue
color_to_char_0 = \ color_0 -> case color_0 of
  Red -> 'R'
  Green -> 'G'
  Blue -> 'B'
|]

  it "type checks" $ runPretty (check IProgram program) `shouldReturn` trim [r|
enum Color = Red | Green | Blue
color_to_char_0 = \ [Color] color_0 -> [Char] case [Color] color_0 of
  [Color] Red -> [Char] 'R'
  [Color] Green -> [Char] 'G'
  [Color] Blue -> [Char] 'B'
|]

  it "evals" $ do
    runEvaluate program "color_to_char Blue" `shouldReturn` "'B'"
