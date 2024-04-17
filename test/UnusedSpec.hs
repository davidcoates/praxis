{-# LANGUAGE QuasiQuotes #-}

module UnusedSpec where

import           Test.Hspec
import           Text.RawString.QQ

import           Util


spec :: Spec
spec = do

  describe "unused variable" $ do

    let program = trim [r|
fst : forall a b. (a, b) -> a
fst (x, y) = x
|]

    it "parses" $ parse program `shouldReturn` trim [r|
fst_0 : forall a_0 b_0 . ( a_0 , b_0 ) -> a_0 = \ ( x_0 , y_0 ) -> x_0
|]

    it "does not type check" $ check program `shouldReturn` "type check error at 2:5: 'y_0' is not used"



  describe "unused underscore" $ do

    let program = trim [r|
fst : forall a b. (a, b) -> a
fst (x, _) = x
|]

    it "parses" $ parse program `shouldReturn` trim [r|
fst_0 : forall a_0 b_0 . ( a_0 , b_0 ) -> a_0 = \ ( x_0 , _ ) -> x_0
|]

    it "type checks" $ check program `shouldReturn` trim [r|
fst_0 : forall a_0 b_0 . ( a_0 , b_0 ) -> a_0 = \ ( [a_0] x_0 , [b_0] _0 ) -> [a_0] x_0
|]



  describe "unused read variable" $ do

    let program = trim [r|
fst : forall a b. (a, b) -> a
fst (x, y) = read y in x
|]

    it "parses" $ parse program `shouldReturn` trim [r|
fst_0 : forall a_0 b_0 . ( a_0 , b_0 ) -> a_0 = \ ( x_0 , y_0 ) -> read y_0 in x_0
|]

    it "does not type checks" $ check program `shouldReturn` "type check error at 2:14: 'y_0' is not used"



  describe "used read variable" $ do

    let program = trim [r|
fst : forall a b. (a, b) -> a
fst (x, y) = read y in x defer y
|]

    it "parses" $ parse program `shouldReturn` trim [r|
fst_0 : forall a_0 b_0 . ( a_0 , b_0 ) -> a_0 = \ ( x_0 , y_0 ) -> read y_0 in x_0 defer y_0
|]

    it "type checks" $ check program `shouldReturn` trim [r|
fst_0 : forall a_0 b_0 . ( a_0 , b_0 ) -> a_0 = \ ( [a_0] x_0 , [b_0] y_0 ) -> read y_0 in [a_0] [a_0] x_0 defer [& 'l0 b_0] y_0
|]

