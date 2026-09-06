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

    it "parses" $ runPretty (parse ProgramT program) `shouldReturn` trim [r|
fst : forall a b . ( a , b ) -> a = \ ( x , y ) -> x
|]

    it "does not type check" $ runPretty (check ProgramT program) `shouldReturn` "type check error at 2:5: variable y is not used"


  describe "unused underscore" $ do

    let program = trim [r|
fst : forall a b | b : Drop. (a, b) -> a
fst (x, _) = x
|]

    it "parses" $ runPretty (parse ProgramT program) `shouldReturn` trim [r|
fst : forall a b | b : Drop . ( a , b ) -> a = \ ( x , _ ) -> x
|]

    it "type checks" $ runPretty (check ProgramT program) `shouldReturn` trim [r|
fst : forall a b | b : Drop . ( a , b ) -> a = \ ( [a] x , [b] hole ) -> [a] x
|]


  describe "unused underscore (not disposable)" $ do

    let program = trim [r|
fst : forall a b. (a, b) -> a
fst (x, _) = x
|]

    it "does not type check" $ runPretty (check ProgramT program) `shouldReturn` trim [r|
type check error: unable to satisfy: b : Drop
  | primary cause: discarded by hole pattern at 2:9
  | secondary cause: function fst with signature forall a b . ( a , b ) -> a at 1:1
|]


  describe "unused underscore (through reference)" $ do

    let program = trim [r|
fst : forall &r a b. &r (a, b) -> &r a
fst (x, _) = x
|]

    it "type checks" $ runPretty (check ProgramT program) `shouldReturn` trim [r|
fst : forall &r a b . &r ( a , b ) -> &r a = \ ( [&r a] x , [&r b] hole ) -> [&r a] x
|]


  describe "unused read variable" $ do

    let program = trim [r|
fst : forall a b. (a, b) -> a
fst (x, y) = read y in x
|]

    it "parses" $ runPretty (parse ProgramT program) `shouldReturn` trim [r|
fst : forall a b . ( a , b ) -> a = \ ( x , y ) -> read y in x
|]

    it "does not type check" $ runPretty (check ProgramT program) `shouldReturn` "type check error at 2:14: variable y is not used in read"


  describe "read only variable" $ do

    let program = trim [r|
fst : forall a b | b : Drop. (a, b) -> a
fst (x, y) = read y in x defer y
|]

    it "parses" $ runPretty (parse ProgramT program) `shouldReturn` trim [r|
fst : forall a b | b : Drop . ( a , b ) -> a = \ ( x , y ) -> read y in x defer y
|]

    it "type checks" $ runPretty (check ProgramT program) `shouldReturn` trim [r|
fst : forall a b | b : Drop . ( a , b ) -> a = \ ( [a] x , [b] y ) -> read y in [a] [a] x defer [&'l0 b] y
|]


  describe "read only variable (not disposable)" $ do

    let program = trim [r|
fst : forall a b. (a, b) -> a
fst (x, y) = read y in x defer y
|]

    it "does not type check" $ runPretty (check ProgramT program) `shouldReturn` trim [r|
type check error: unable to satisfy: b : Drop
  | primary cause: variable y is not consumed at 2:5
  | secondary cause: function fst with signature forall a b . ( a , b ) -> a at 1:1
|]


  describe "unused type variable" $ do

    let ty = trim [r|
forall a b. a
|]

    it "parses" $ runPretty (parse QTypeT ty) `shouldReturn` trim [r|
forall a b . a
|]

    -- TODO should have a better error message here!
    it "does not type check" $ runPretty (check QTypeT ty) `shouldReturn` trim [r|
kind check error: unsolved constraints: plain ^k0, plain ^k1
|]
