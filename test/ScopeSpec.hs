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

    it "does not parse" $ parse program `shouldReturn` trim [r|
parse error at 2:5: variables are not distinct
|]


  describe "type variarble redeclaration" $ do

    let program = trim [r|
datatype Foo [a, a] = Foo a
|]

    it "does not parse" $ parse program `shouldReturn` "parse error at 1:14: type variables are not distinct"



  describe "type redeclaration" $ do

    let program = trim [r|
datatype Foo = Foo ()
enum Foo = Bar | Baz
|]

    it "does not check" $ check program `shouldReturn` "kind check error at 2:1: type 'Foo' redeclared"



  describe "constructor redeclaration" $ do

    let program = trim [r|
datatype FooData = Foo ()
enum FooEnum = Foo | Bar
|]

    it "does not check" $ check program `shouldReturn` "type check error at 2:1: constructor 'Foo' redeclared"



  describe "term redeclaration" $ do

    let program = trim [r|
x = 1
x = 2
|]

    it "does not check" $ check program `shouldReturn` "parse error at 1:1: multiple definitions for 'x'"



  describe "out of scope term" $ do

    let program = trim [r|
x = y where y = 1
z = y
|]

    it "does not check" $ check program `shouldReturn` "type check error at 2:5: 'y' is not in scope"


  describe "out of scope non-recursive function" $ do

    let program = trim [r|
x () = x ()
|]

    it "does not check" $ check program `shouldReturn` "type check error at 1:8: 'x' is not in scope"



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

    it "parses" $ parse program `shouldReturn` trim [r|
f_0 = \ x_0 -> f_1 x_0 where
  f_1 : I32 -> I32 = \ x_1 -> x_1
g_0 = \ x_2 -> f_2 x_2 where
  rec
    f_2 = cases
      0 -> 1
      n_0 -> multiply ( f_2 subtract ( n_0 , 1 ) , n_0 )
h_0 = \ x_3 -> f_3 x_3 where
  f_3 = cases
    0 -> 1
    n_1 -> multiply ( f_0 subtract ( n_1 , 1 ) , n_1 )
|]

    it "type checks" $ check program `shouldReturn` trim [r|
f_0 = \ [I32] x_0 -> [I32] [I32 -> I32] f_1 [I32] x_0 where
  f_1 : I32 -> I32 = \ [I32] x_1 -> [I32] x_1
g_0 = \ [I32] x_2 -> [I32] [I32 -> I32] f_2 [I32] x_2 where
  rec
    f_2 = [I32 -> I32] cases
      [I32] 0 -> [I32] 1
      [I32] n_0 -> [( I32 , I32 ) -> I32] multiply ( [I32 -> I32] f_2 [( I32 , I32 ) -> I32] subtract ( [I32] n_0 , [I32] 1 ) , [I32] n_0 )
h_0 = \ [I32] x_3 -> [I32] [I32 -> I32] f_3 [I32] x_3 where
  f_3 = [I32 -> I32] cases
    [I32] 0 -> [I32] 1
    [I32] n_1 -> [( I32 , I32 ) -> I32] multiply ( [I32 -> I32] f_0 [( I32 , I32 ) -> I32] subtract ( [I32] n_1 , [I32] 1 ) , [I32] n_1 )
|]

    it "evaluates" $ do
      evaluate program "f 5" `shouldReturn` "5"
      evaluate program "g 5" `shouldReturn` "120"
