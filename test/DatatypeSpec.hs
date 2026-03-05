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

    it "parses" $ runPretty (parse ProgramT program) `shouldReturn` trim [r|
datatype unboxed Either a b = Left a | Right b
|]

    it "type checks" $ runPretty (check ProgramT program) `shouldReturn` trim [r|
datatype unboxed Either a b = [forall a b . a -> Either a b] Left a | [forall a b . b -> Either a b] Right b
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

    it "parses" $ runPretty (parse ProgramT program) `shouldReturn` trim [r|
datatype unboxed Fun a b = Fun ( a -> b )
unbox_fun : forall a b . Fun a b -> a -> b = \ Fun f -> \ x -> f x
id_fun : forall a . ( ) -> Fun a a = \ ( ) -> Fun ( \ x -> x )
|]

    it "type checks" $ runPretty (check ProgramT program) `shouldReturn` trim [r|
datatype unboxed Fun a b = [forall a b . ( a -> b ) -> Fun a b] Fun ( a -> b )
unbox_fun : forall a b . Fun a b -> a -> b = \ [Fun a b] Fun [a -> b] f -> \ [a] x -> [a -> b] f [a] x
id_fun : forall a . ( ) -> Fun a a = \ [( )] ( ) -> [( a -> a ) -> Fun a a] Fun ( \ [a] x -> [a] x )
|]

    it "evals" $ runEvaluate program "unbox_fun (id_fun ()) 4"  `shouldReturn` "4"


  describe "datatype Unboxed (unboxed)" $ do

    let program = [r|
datatype unboxed Unboxed a = Unboxed a
|]

    it "type checks" $ runPretty (check ProgramT program) `shouldReturn` trim [r|
datatype unboxed Unboxed a = [forall a . a -> Unboxed a] Unboxed a
|]


  describe "datatype Boxed (boxed)" $ do

    let program = [r|
datatype boxed Boxed a = Boxed a
|]

    it "type checks" $ runPretty (check ProgramT program) `shouldReturn` trim [r|
datatype boxed Boxed a = [forall a . a -> Boxed a] Boxed a
|]


  describe "datatype List (non-rec fails)" $ do

    let program = [r|
datatype List a = Nil () | Cons (a, List a)
|]

    it "type checks" $ runPretty (check ProgramT program) `shouldReturn` trim [r|
kind check error at 2:37: type List is not in scope
|]


  describe "datatype List (rec, with map & sum)" $ do

    let program = [r|
rec datatype List a = Nil () | Cons (a, List a)

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

    it "parses" $ runPretty (parse ProgramT program) `shouldReturn` trim [r|
rec
  datatype boxed List a = Nil ( ) | Cons ( a , List a )
rec
  map : forall ?v a b . ( ?v a -> b ) -> ?v List a -> List b = \ f -> cases
    Nil ( ) -> Nil ( )
    Cons ( x , xs ) -> Cons ( f x , map f xs )
rec
  sum : forall &r . &r List I32 -> I32 = cases
    Nil ( ) -> 0
    Cons ( x , xs ) -> add ( x , sum xs )
|]

    it "type checks" $ runPretty (check ProgramT program) `shouldReturn` trim [r|
rec
  datatype boxed List a = [forall a . ( ) -> List a] Nil ( ) | [forall a . ( a , List a ) -> List a] Cons ( a , List a )
rec
  map : forall ?v a b . ( ?v a -> b ) -> ?v List a -> List b = \ [?v a -> b] f -> [?v List a -> List b] cases
    [?v List a] Nil [( )] ( ) -> [( ) -> List b] Nil [( )] ( )
    [?v List a] Cons ( [?v a] x , [?v List a] xs ) -> [( b , List b ) -> List b] Cons ( [?v a -> b] f [?v a] x , [( ?v a -> b ) -> ?v List a -> List b] map [?v a -> b] f [?v List a] xs )
rec
  sum : forall &r . &r List I32 -> I32 = [&r List I32 -> I32] cases
    [&r List I32] Nil [( )] ( ) -> [I32] 0
    [&r List I32] Cons ( [I32] x , [&r List I32] xs ) -> [( I32 , I32 ) -> I32] add ( [I32] x , [&r List I32 -> I32] sum [&r List I32] xs )
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
