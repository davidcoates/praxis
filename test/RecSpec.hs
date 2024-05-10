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
    0 -> 1 : I64
    n -> n * fac (n - 1)
|]

    it "parses" $ parse program `shouldReturn` trim [r|
rec
  fac_0 = cases
    0 -> 1 : I64
    n_0 -> multiply ( n_0 , fac_0 subtract ( n_0 , 1 ) )
|]

    it "type checks" $ check program `shouldReturn` trim [r|
rec
  fac_0 = [I64 -> I64] cases
    [I64] 0 -> [I64] 1 : I64
    [I64] n_0 -> [( I64 , I64 ) -> I64] multiply ( [I64] n_0 , [I64 -> I64] fac_0 [( I64 , I64 ) -> I64] subtract ( [I64] n_0 , [I64] 1 ) )
|]

    it "evaluates" $ do
      evaluate program "fac 0"  `shouldReturn` "1"
      evaluate program "fac 5"  `shouldReturn` "120"
      evaluate program "fac 15" `shouldReturn` "1307674368000"


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
    n_0 -> is_odd_0 subtract ( n_0 , 1 )
  is_odd_0 = cases
    0 -> False
    n_1 -> is_even_0 subtract ( n_1 , 1 )
|]

    it "type checks" $ check program `shouldReturn` trim [r|
rec
  is_even_0 = [I32 -> Bool] cases
    [I32] 0 -> [Bool] True
    [I32] n_0 -> [I32 -> Bool] is_odd_0 [( I32 , I32 ) -> I32] subtract ( [I32] n_0 , [I32] 1 )
  is_odd_0 = [I32 -> Bool] cases
    [I32] 0 -> [Bool] False
    [I32] n_1 -> [I32 -> Bool] is_even_0 [( I32 , I32 ) -> I32] subtract ( [I32] n_1 , [I32] 1 )
|]

    it "evaluates" $ do
      evaluate program "is_even 0" `shouldReturn` "True"
      evaluate program "is_even 1" `shouldReturn` "False"
      evaluate program "is_even 2" `shouldReturn` "True"
      evaluate program "is_even 3" `shouldReturn` "False"
      evaluate program "is_odd 0" `shouldReturn` "False"
      evaluate program "is_odd 1" `shouldReturn` "True"
      evaluate program "is_odd 2" `shouldReturn` "False"
      evaluate program "is_odd 3" `shouldReturn` "True"
