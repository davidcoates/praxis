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
2:5 error: variables are not distinct
|]


  describe "type variarble redeclaration" $ do

    let program = trim [r|
datatype Foo [a, a] = Foo a
|]

    it "does not parse" $ parse program `shouldReturn` "1:14 error: type variables are not distinct"



  describe "type redeclaration" $ do

    let program = trim [r|
datatype Foo = Foo ()
enum Foo = Bar | Baz
|]

    it "does not check" $ check program `shouldReturn` "2:1 error: type 'Foo' redeclared"



  describe "constructor redeclaration" $ do

    let program = trim [r|
datatype FooData = Foo ()
enum FooEnum = Foo | Bar
|]

    it "does not check" $ check program `shouldReturn` "2:1 error: constructor 'Foo' redeclared"



  describe "term redeclaration" $ do

    let program = trim [r|
x = 1
x = 2
|]

    it "does not check" $ check program `shouldReturn` "1:1 error: multiple definitions for 'x'"



  describe "out of scope term" $ do

    let program = trim [r|
x = y where y = 1
z = y
|]

    it "does not check" $ check program `shouldReturn` "2:5 error: 'y' is not in scope"


  describe "out of scope non-recursive function" $ do

    let program = trim [r|
x () = x ()
|]

    it "does not check" $ check program `shouldReturn` "1:8 error: 'x' is not in scope"



  describe "shadowing" $ do

    let program = [r|
f x = f x where
  f : Int -> Int
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
  f_1 : Int -> Int = \ x_1 -> x_1
g_0 = \ x_2 -> f_2 x_2 where
  rec
    f_2 = cases
      0 -> 1
      n_0 -> multiply_int ( f_2 subtract_int ( n_0 , 1 ) , n_0 )
h_0 = \ x_3 -> f_3 x_3 where
  f_3 = cases
    0 -> 1
    n_1 -> multiply_int ( f_0 subtract_int ( n_1 , 1 ) , n_1 )
|]

    it "type checks" $ check program `shouldReturn` trim [r|
f_0 = \ [Int] x_0 -> [Int] [Int -> Int] f_1 [Int] x_0 where
  f_1 : Int -> Int = \ [Int] x_1 -> [Int] x_1
g_0 = \ [Int] x_2 -> [Int] [Int -> Int] f_2 [Int] x_2 where
  rec
    f_2 = [Int -> Int] cases
      [Int] 0 -> [Int] 1
      [Int] n_0 -> [( Int , Int ) -> Int] multiply_int ( [Int -> Int] f_2 [( Int , Int ) -> Int] subtract_int ( [Int] n_0 , [Int] 1 ) , [Int] n_0 )
h_0 = \ [Int] x_3 -> [Int] [Int -> Int] f_3 [Int] x_3 where
  f_3 = [Int -> Int] cases
    [Int] 0 -> [Int] 1
    [Int] n_1 -> [( Int , Int ) -> Int] multiply_int ( [Int -> Int] f_0 [( Int , Int ) -> Int] subtract_int ( [Int] n_1 , [Int] 1 ) , [Int] n_1 )
|]

    it "evaluates" $ do
      interpret program "f 5" `shouldReturn` "5"
      interpret program "g 5" `shouldReturn` "120"
