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

    it "does not check" $ runPretty (check IProgram program) `shouldReturn` trim [r|
type check error at 2:5: variables are not distinct
|]


  describe "type variarble redeclaration" $ do

    let program = trim [r|
datatype Foo a a = Foo a
|]

    it "does not check" $ runPretty (check IProgram program) `shouldReturn` "kind check error at 1:1: variables are not distinct"


    let program = trim [r|
datatype Foo a &a = Foo a
|]

    it "does not check" $ runPretty (check IProgram program) `shouldReturn` "kind check error at 1:1: variables are not distinct"


    let program = trim [r|
datatype Foo ?a &a = Foo &a
|]

    it "does not check" $ runPretty (check IProgram program) `shouldReturn` "kind check error at 1:1: variables are not distinct"


  describe "type redeclaration" $ do

    let program = trim [r|
datatype Foo = Foo ()
enum Foo = Bar | Baz
|]

    it "does not check" $ runPretty (check IProgram program) `shouldReturn` "kind check error at 2:1: type 'Foo' redeclared"


  describe "constructor redeclaration" $ do

    let program = trim [r|
datatype FooData = Foo ()
enum FooEnum = Foo | Bar
|]

    it "does not check" $ runPretty (check IProgram program) `shouldReturn` "type check error at 2:1: constructor 'Foo' redeclared"


  describe "term redeclaration" $ do

    let program = trim [r|
x = 1
x = 2
|]

    it "checks" $ runPretty (check IProgram program) `shouldReturn` trim [r|
x_0 = [I32] 1
x_1 = [I32] 2
|]


  describe "out of scope term" $ do

    let program = trim [r|
x = y where y = 1
z = y
|]

    it "does not check" $ runPretty (check IProgram program) `shouldReturn` "type check error at 2:5: variable 'y' is not in scope"


  describe "out of scope non-recursive function" $ do

    let program = trim [r|
x () = x ()
|]

    it "does not check" $ runPretty (check IProgram program) `shouldReturn` "type check error at 1:8: variable 'x' is not in scope"


  describe "shadowing" $ do

    let program = [r|
f x = f x where
  f : I32 -> I32
  f x = x

g x = f x where rec
  f = cases
    0 -> 1
    n -> f (n - 1) * n

h x = f x where
  f = cases
    0 -> 1
    n -> f (n - 1) * n
|]

    it "type checks" $ runPretty (check IProgram program) `shouldReturn` trim [r|
f_1 = \ [I32] x_0 -> [I32] [I32 -> I32] f_0 [I32] x_0 where
  f_0 : I32 -> I32 = \ [I32] x_1 -> [I32] x_1
g_0 = \ [I32] x_2 -> [I32] [I32 -> I32] f_2 [I32] x_2 where
  rec
    f_2 = [I32 -> I32] cases
      [I32] 0 -> [I32] 1
      [I32] n_0 -> [( I32 , I32 ) -> I32] multiply_0 ( [I32 -> I32] f_2 ( [( I32 , I32 ) -> I32] subtract_0 ( [I32] n_0 , [I32] 1 ) ) , [I32] n_0 )
h_0 = \ [I32] x_3 -> [I32] [I32 -> I32] f_3 [I32] x_3 where
  f_3 = [I32 -> I32] cases
    [I32] 0 -> [I32] 1
    [I32] n_1 -> [( I32 , I32 ) -> I32] multiply_0 ( [I32 -> I32] f_1 ( [( I32 , I32 ) -> I32] subtract_0 ( [I32] n_1 , [I32] 1 ) ) , [I32] n_1 )
|]

    it "evals" $ do
      runEvaluate program "f 5" `shouldReturn` "5"
      runEvaluate program "g 5" `shouldReturn` "120"
