{-# LANGUAGE QuasiQuotes #-}

module UnusedSpec where

import           Test.Hspec
import           Text.RawString.QQ

import           Introspect
import           Util


spec :: Spec
spec = do

  describe "unused variable" $ do

    let program = trim [r|
fst : forall a b. (a, b) -> a
fst (x, y) = x
|]

    it "parses" $ runPretty (parse IProgram program) `shouldReturn` trim [r|
fst : forall a b . ( a , b ) -> a = \ ( x , y ) -> x
|]

    it "does not type check" $ runPretty (check IProgram program) `shouldReturn` "type check error at 2:5: variable y is not used"


  describe "unused underscore" $ do

    let program = trim [r|
fst : forall a b. (a, b) -> a
fst (x, _) = x
|]

    it "parses" $ runPretty (parse IProgram program) `shouldReturn` trim [r|
fst : forall a b . ( a , b ) -> a = \ ( x , _ ) -> x
|]

    it "type checks" $ runPretty (check IProgram program) `shouldReturn` trim [r|
fst_0 : forall a_0 b_0 . ( a_0 , b_0 ) -> a_0 = \ ( [a_0] x_0 , [b_0] _hole_0 ) -> [a_0] x_0
|]


  describe "unused read variable" $ do

    let program = trim [r|
fst : forall a b. (a, b) -> a
fst (x, y) = read y in x
|]

    it "parses" $ runPretty (parse IProgram program) `shouldReturn` trim [r|
fst : forall a b . ( a , b ) -> a = \ ( x , y ) -> read y in x
|]

    it "does not type check" $ runPretty (check IProgram program) `shouldReturn` "type check error at 2:14: variable y is not used in read"


  describe "used read variable" $ do

    let program = trim [r|
fst : forall a b. (a, b) -> a
fst (x, y) = read y in x defer y
|]

    it "parses" $ runPretty (parse IProgram program) `shouldReturn` trim [r|
fst : forall a b . ( a , b ) -> a = \ ( x , y ) -> read y in x defer y
|]

    it "type checks" $ runPretty (check IProgram program) `shouldReturn` trim [r|
fst_0 : forall a_0 b_0 . ( a_0 , b_0 ) -> a_0 = \ ( [a_0] x_0 , [b_0] y_0 ) -> read y_0 in [a_0] [a_0] x_0 defer [&'l0 b_0] y_0
|]


  describe "unused type variable" $ do

    let ty = trim [r|
forall a b. a
|]

    it "parses" $ runPretty (parse IQType ty) `shouldReturn` trim [r|
forall a b . a
|]

    -- TODO should have a better error message here!
    it "does not type check" $ runPretty (check IQType ty) `shouldReturn` trim [r|
kind check error: unsolved constraints: Plain ^k0, Plain ^k1
|]
