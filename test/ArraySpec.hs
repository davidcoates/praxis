{-# LANGUAGE QuasiQuotes #-}

module ArraySpec where

import           Test.Hspec
import           Text.RawString.QQ

import           Introspect
import           Util


spec :: Spec
spec = do

  describe "new array" $ do

    let program = [r|
xs : Array I32
xs = new_array (3, \() -> 7)

empty : Array I32
empty = new_array (0, \() -> 7)
|]

    it "evals" $ do
      runEvaluate program "xs" `shouldReturn` "[7, 7, 7]"
      runEvaluate program "len_array xs" `shouldReturn` "3"
      runEvaluate program "empty" `shouldReturn` "[]"
      runEvaluate program "len_array empty" `shouldReturn` "0"
