{-# LANGUAGE QuasiQuotes #-}

module DatatypeSpec where

import           Test.Hspec
import           Text.RawString.QQ

import           Util


spec :: Spec
spec = do

  describe "datatype Either" $ do

    let program = [r|
datatype Either [a, b] = Left a | Right b
|]

    it "parses" $ parse program `shouldReturn` trim [r|
datatype unboxed Either [ a_0 , b_0 ] = Left a_0 | Right b_0
|]

    it "type checks" $ check program `shouldReturn` trim [r|
datatype unboxed Either [ a_0 , b_0 ] = [forall a_0 b_0 . a_0 -> Either [ a_0 , b_0 ]] Left a_0 | [forall a_0 b_0 . b_0 -> Either [ a_0 , b_0 ]] Right b_0
|]

    it "evaluates" $ do
      evaluate program "Left 0 : Either [I32, ()]"  `shouldReturn` "Left 0"
      evaluate program "Right 1 : Either [(), I32]" `shouldReturn` "Right 1"



  describe "datatype Fun (with unbox)" $ do

    let program = [r|
datatype Fun [a, b] = Fun (a -> b)

unbox_fun : forall a b. Fun [a, b] -> a -> b
unbox_fun (Fun f) x = f x

-- FIXME unit shouldn't be required here since Fun [a, a] is shareable
id_fun : forall a. () -> Fun [a, a]
id_fun () = Fun (\x -> x)
|]

    it "parses" $ parse program `shouldReturn` trim [r|
datatype unboxed Fun [ a_0 , b_0 ] = Fun ( a_0 -> b_0 )
unbox_fun_0 : forall a_1 b_1 . Fun [ a_1 , b_1 ] -> a_1 -> b_1 = \ Fun f_0 -> \ x_0 -> f_0 x_0
id_fun_0 : forall a_2 . ( ) -> Fun [ a_2 , a_2 ] = \ ( ) -> Fun ( \ x_1 -> x_1 )
|]

    it "type checks" $ check program `shouldReturn` trim [r|
datatype unboxed Fun [ a_0 , b_0 ] = [forall a_0 b_0 . ( a_0 -> b_0 ) -> Fun [ a_0 , b_0 ]] Fun ( a_0 -> b_0 )
unbox_fun_0 : forall a_1 b_1 . Fun [ a_1 , b_1 ] -> a_1 -> b_1 = \ [Fun [ a_1 , b_1 ]] Fun [a_1 -> b_1] f_0 -> \ [a_1] x_0 -> [a_1 -> b_1] f_0 [a_1] x_0
id_fun_0 : forall a_2 . ( ) -> Fun [ a_2 , a_2 ] = \ [( )] ( ) -> [( a_2 -> a_2 ) -> Fun [ a_2 , a_2 ]] Fun ( \ [a_2] x_1 -> [a_2] x_1 )
|]

    it "evaluates" $ evaluate program "(unbox_fun id_fun ()) 4"  `shouldReturn` "4"



  describe "datatype Unboxed (unboxed)" $ do

    let program = [r|
datatype unboxed Unboxed a = Unboxed a
|]

    it "type checks" $ check program `shouldReturn` trim [r|
datatype unboxed Unboxed a_0 = [forall a_0 . a_0 -> Unboxed a_0] Unboxed a_0
|]

    it "translates" $ translate program `shouldReturn` trim [r|
TODO
|]


  describe "datatype Boxed (boxed)" $ do

    let program = [r|
datatype boxed Boxed a = Boxed a
|]

    it "type checks" $ check program `shouldReturn` trim [r|
datatype boxed Boxed a_0 = [forall a_0 . a_0 -> Boxed a_0] Boxed a_0
|]

    it "translates" $ translate program `shouldReturn` trim [r|
TODO
|]



  describe "datatype List (non-rec fails)" $ do

    let program = [r|
datatype List a = Nil () | Cons (a, List a)
|]

    it "type checks" $ check program `shouldReturn` trim [r|
kind check error at 2:37: 'List' is not in scope
|]



  describe "datatype List (rec, with map & sum)" $ do

    let program = [r|
datatype rec List a = Nil () | Cons (a, List a)

rec
  map : forall ?v a b. (?v a -> b) -> ?v List a -> List b
  map f = cases
    Nil ()       -> Nil ()
    Cons (x, xs) -> Cons (f x, (map f) xs)

rec
  sum : forall &r. &r List I32 -> I32
  sum = cases
    Nil ()       -> 0
    Cons (x, xs) -> x + sum xs
|]

    it "parses" $ parse program `shouldReturn` trim [r|
datatype rec List a_0 = Nil ( ) | Cons ( a_0 , List a_0 )
rec
  map_0 : forall ? v_0 a_1 b_0 . ( ? v_0 a_1 -> b_0 ) -> ? v_0 List a_1 -> List b_0 = \ f_0 -> cases
    Nil ( ) -> Nil ( )
    Cons ( x_0 , xs_0 ) -> Cons ( f_0 x_0 , ( map_0 f_0 ) xs_0 )
rec
  sum_0 : forall & r_0 . & r_0 List I32 -> I32 = cases
    Nil ( ) -> 0
    Cons ( x_1 , xs_1 ) -> add ( x_1 , sum_0 xs_1 )
|]

    it "type checks" $ check program `shouldReturn` trim [r|
datatype rec List a_0 = [forall a_0 . ( ) -> List a_0] Nil ( ) | [forall a_0 . ( a_0 , List a_0 ) -> List a_0] Cons ( a_0 , List a_0 )
rec
  map_0 : forall ? v_0 a_1 b_0 . ( ? v_0 a_1 -> b_0 ) -> ? v_0 List a_1 -> List b_0 = \ [? v_0 a_1 -> b_0] f_0 -> [? v_0 List a_1 -> List b_0] cases
    [? v_0 List a_1] Nil [( )] ( ) -> [( ) -> List b_0] Nil [( )] ( )
    [? v_0 List a_1] Cons ( [? v_0 a_1] x_0 , [? v_0 List a_1] xs_0 ) -> [( b_0 , List b_0 ) -> List b_0] Cons ( [? v_0 a_1 -> b_0] f_0 [? v_0 a_1] x_0 , ( [( ? v_0 a_1 -> b_0 ) -> ? v_0 List a_1 -> List b_0] map_0 [? v_0 a_1 -> b_0] f_0 ) [? v_0 List a_1] xs_0 )
rec
  sum_0 : forall & r_0 . & r_0 List I32 -> I32 = [& r_0 List I32 -> I32] cases
    [& r_0 List I32] Nil [( )] ( ) -> [I32] 0
    [& r_0 List I32] Cons ( [I32] x_1 , [& r_0 List I32] xs_1 ) -> [( I32 , I32 ) -> I32] add ( [I32] x_1 , [& r_0 List I32 -> I32] sum_0 [& r_0 List I32] xs_1 )
|]

    it "translates" $ translate program `shouldReturn` trim [r|
TODO
|]

    it "evaluates" $ do

      evaluate program [r|
do
  let xs = Cons (1, Cons (2, Cons (3, Nil ())))
  sum &xs
|] `shouldReturn` "6"

      evaluate program [r|
do
  let xs = Cons (1, Cons (2, Cons (3, Nil ())))
  let ys = (map (\x -> x * 2)) &xs
  sum &ys
|] `shouldReturn` "12"
