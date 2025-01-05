{-# LANGUAGE QuasiQuotes #-}

module DatatypeSpec where

import           Test.Hspec
import           Text.RawString.QQ

import           Introspect
import           Util


spec :: Spec
spec = do

  describe "datatype Either" $ do

    let program = [r|
datatype Either a b = Left a | Right b
|]

    it "parses" $ runPretty (parse IProgram program) `shouldReturn` trim [r|
datatype unboxed Either a b = Left a | Right b
|]

    it "type checks" $ runPretty (check IProgram program) `shouldReturn` trim [r|
datatype unboxed Either a_0 b_0 = [forall a_0 b_0 . a_0 -> Either a_0 b_0] Left a_0 | [forall a_0 b_0 . b_0 -> Either a_0 b_0] Right b_0
|]

    it "evals" $ do
      runEvaluate program "Left 0 : Either I32 ()"  `shouldReturn` "Left 0"
      runEvaluate program "Right 1 : Either () I32" `shouldReturn` "Right 1"


  describe "datatype Fun (with unbox)" $ do

    let program = [r|
datatype Fun a b = Fun (a -> b)

unbox_fun : forall a b. Fun a b -> a -> b
unbox_fun (Fun f) x = f x

-- FIXME unit shouldn't be required here since Fun [a, a] is shareable
id_fun : forall a. () -> Fun a a
id_fun () = Fun (\x -> x)
|]

    it "parses" $ runPretty (parse IProgram program) `shouldReturn` trim [r|
datatype unboxed Fun a b = Fun ( a -> b )
unbox_fun : forall a b . Fun a b -> a -> b = \ Fun f -> \ x -> f x
id_fun : forall a . ( ) -> Fun a a = \ ( ) -> Fun ( \ x -> x )
|]

    it "type checks" $ runPretty (check IProgram program) `shouldReturn` trim [r|
datatype unboxed Fun a_0 b_0 = [forall a_0 b_0 . ( a_0 -> b_0 ) -> Fun a_0 b_0] Fun ( a_0 -> b_0 )
unbox_fun_0 : forall a_1 b_1 . Fun a_1 b_1 -> a_1 -> b_1 = \ [Fun a_1 b_1] Fun [a_1 -> b_1] f_0 -> \ [a_1] x_0 -> [a_1 -> b_1] f_0 [a_1] x_0
id_fun_0 : forall a_2 . ( ) -> Fun a_2 a_2 = \ [( )] ( ) -> [( a_2 -> a_2 ) -> Fun a_2 a_2] Fun ( \ [a_2] x_1 -> [a_2] x_1 )
|]

    it "evals" $ runEvaluate program "unbox_fun (id_fun ()) 4"  `shouldReturn` "4"


  describe "datatype Unboxed (unboxed)" $ do

    let program = [r|
datatype unboxed Unboxed a = Unboxed a
|]

    it "type checks" $ runPretty (check IProgram program) `shouldReturn` trim [r|
datatype unboxed Unboxed a_0 = [forall a_0 . a_0 -> Unboxed a_0] Unboxed a_0
|]


  describe "datatype Boxed (boxed)" $ do

    let program = [r|
datatype boxed Boxed a = Boxed a
|]

    it "type checks" $ runPretty (check IProgram program) `shouldReturn` trim [r|
datatype boxed Boxed a_0 = [forall a_0 . a_0 -> Boxed a_0] Boxed a_0
|]


  describe "datatype List (non-rec fails)" $ do

    let program = [r|
datatype List a = Nil () | Cons (a, List a)
|]

    it "type checks" $ runPretty (check IProgram program) `shouldReturn` trim [r|
kind check error at 2:37: type List is not in scope
|]


  describe "datatype List (rec, with map & sum)" $ do

    let program = [r|
datatype rec List a = Nil () | Cons (a, List a)

rec
  map : forall ?v a b. (?v a -> b) -> ?v List a -> List b
  map f = cases
    Nil ()       -> Nil ()
    Cons (x, xs) -> Cons (f x, map f xs)

rec
  sum : forall &r. &r List I32 -> I32
  sum = cases
    Nil ()       -> 0
    Cons (x, xs) -> x + sum xs
|]

    it "parses" $ runPretty (parse IProgram program) `shouldReturn` trim [r|
datatype rec List a = Nil ( ) | Cons ( a , List a )
rec
  map : forall ?v a b . ( ?v a -> b ) -> ?v List a -> List b = \ f -> cases
    Nil ( ) -> Nil ( )
    Cons ( x , xs ) -> Cons ( f x , map f xs )
rec
  sum : forall &r . &r List I32 -> I32 = cases
    Nil ( ) -> 0
    Cons ( x , xs ) -> add ( x , sum xs )
|]

    it "type checks" $ runPretty (check IProgram program) `shouldReturn` trim [r|
datatype rec List a_0 = [forall a_0 . ( ) -> List a_0] Nil ( ) | [forall a_0 . ( a_0 , List a_0 ) -> List a_0] Cons ( a_0 , List a_0 )
rec
  map_0 : forall ?v_0 a_1 b_0 . ( ?v_0 a_1 -> b_0 ) -> ?v_0 List a_1 -> List b_0 = \ [?v_0 a_1 -> b_0] f_0 -> [?v_0 List a_1 -> List b_0] cases
    [?v_0 List a_1] Nil [( )] ( ) -> [( ) -> List b_0] Nil [( )] ( )
    [?v_0 List a_1] Cons ( [?v_0 a_1] x_0 , [?v_0 List a_1] xs_0 ) -> [( b_0 , List b_0 ) -> List b_0] Cons ( [?v_0 a_1 -> b_0] f_0 [?v_0 a_1] x_0 , [( ?v_0 a_1 -> b_0 ) -> ?v_0 List a_1 -> List b_0] map_0 [?v_0 a_1 -> b_0] f_0 [?v_0 List a_1] xs_0 )
rec
  sum_0 : forall &r_0 . &r_0 List I32 -> I32 = [&r_0 List I32 -> I32] cases
    [&r_0 List I32] Nil [( )] ( ) -> [I32] 0
    [&r_0 List I32] Cons ( [I32] x_1 , [&r_0 List I32] xs_1 ) -> [( I32 , I32 ) -> I32] add ( [I32] x_1 , [&r_0 List I32 -> I32] sum_0 [&r_0 List I32] xs_1 )
|]

    it "evals" $ do

      runEvaluate program [r|
do
  let xs = Cons (1, Cons (2, Cons (3, Nil ())))
  sum &xs
|] `shouldReturn` "6"

      runEvaluate program [r|
do
  let xs = Cons (1, Cons (2, Cons (3, Nil ())))
  let ys = map (\x -> x * 2) &xs
  sum &ys
|] `shouldReturn` "12"
