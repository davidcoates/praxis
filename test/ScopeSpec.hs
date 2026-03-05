{-# LANGUAGE QuasiQuotes #-}

module ScopeSpec where

import           Control.Monad     (forM_)
import           Test.Hspec
import           Text.RawString.QQ

import           Introspect
import           Util


spec :: Spec
spec = do

  describe "variable redeclaration" $ do

    let program = trim [r|
fst : forall a. (a, a) -> a
fst (a, a) = a
|]

    it "does not check" $ runPretty (check ProgramT program) `shouldReturn` trim [r|
type check error at 2:5: variables are not distinct
|]


  describe "type variarble redeclaration" $ do

    let program = trim [r|
datatype Foo a a = Foo a
|]

    it "does not check" $ runPretty (check ProgramT program) `shouldReturn` "kind check error at 1:1: type variables are not distinct"


    let program = trim [r|
datatype Foo a &a = Foo a
|]

    it "does not check" $ runPretty (check ProgramT program) `shouldReturn` "kind check error at 1:1: type variables are not distinct"


    let program = trim [r|
datatype Foo ?a &a = Foo &a
|]

    it "does not check" $ runPretty (check ProgramT program) `shouldReturn` "kind check error at 1:1: type variables are not distinct"


    let program = trim [r|
datatype Foo !a = Foo a
|]

    it "does not check" $ runPretty (check ProgramT program) `shouldReturn` "kind check error at 1:23: type variable a has the wrong flavor"


  describe "type redeclaration" $ do

    let program = trim [r|
datatype Foo = Foo ()
enum Foo = Bar | Baz
|]

    it "does not check" $ runPretty (check ProgramT program) `shouldReturn` "kind check error at 2:1: type Foo redeclared"


  describe "constructor redeclaration" $ do

    let program = trim [r|
datatype FooData = Foo ()
enum FooEnum = Foo | Bar
|]

    it "does not check" $ runPretty (check ProgramT program) `shouldReturn` "type check error at 2:1: constructor Foo redeclared"


  describe "term redeclaration" $ do

    let program = trim [r|
x = 1
x = 2
|]

    it "checks" $ runPretty (check ProgramT program) `shouldReturn` trim [r|
x = [I32] 1
x = [I32] 2
|]


  describe "out of scope term" $ do

    let program = trim [r|
x = y where y = 1
z = y
|]

    it "does not check" $ runPretty (check ProgramT program) `shouldReturn` "type check error at 2:5: variable y is not in scope"


  describe "out of scope non-recursive function" $ do

    let program = trim [r|
x () = x ()
|]

    it "does not check" $ runPretty (check ProgramT program) `shouldReturn` "type check error at 1:8: variable x is not in scope"


  describe "shadowing" $ do

    let program = [r|
f x = f x where
  f : I32 -> I32
  f x = x

g x = f x where
  f = cases
    0 -> 1
    n -> f (n - 1) * n
|]

    it "type checks" $ runPretty (check ProgramT program) `shouldReturn` trim [r|
f = \ [I32] x -> [I32] [I32 -> I32] f [I32] x where
  f : I32 -> I32 = \ [I32] x -> [I32] x
g = \ [I32] x -> [I32] [I32 -> I32] f [I32] x where
  f = [I32 -> I32] cases
    [I32] 0 -> [I32] 1
    [I32] n -> [( I32 , I32 ) -> I32] multiply ( [I32 -> I32] f ( [( I32 , I32 ) -> I32] subtract ( [I32] n , [I32] 1 ) ) , [I32] n )
|]

    it "evals" $ do
      runEvaluate program "f 5" `shouldReturn` "5"
      runEvaluate program "g 5" `shouldReturn` "20"
