{-# LANGUAGE QuasiQuotes #-}

module CopySpec where

import           Test.Hspec
import           Text.RawString.QQ

import           Util


spec :: Spec
spec = do

  describe "boxed type" $ do

    describe "no copy constraint" $ do

      let program = [r|
datatype boxed Boxed a = Boxed a

copy : forall a . Boxed a -> (Boxed a, Boxed a)
copy x = (x, x)
|]

      it "does not type check" $ check program  `shouldReturn` trim [r|
type check error: unable to satisfy: Copy Boxed a_1
  | primary cause: variable 'x_0' used more than once at 5:14
  | secondary cause: function signature for 'copy_0' at 4:1
|]



    describe "trivial copy constraint" $ do

      let program = [r|
datatype boxed Boxed a = Boxed a

copy : forall a | Copy (Boxed a) . Boxed a -> (Boxed a, Boxed a)
copy x = (x, x)

foo = copy Boxed 1
|]

      it "does not type check" $ check program  `shouldReturn` trim [r|
type check error: unable to satisfy: Copy Boxed ^t2
  | primary cause: specialisation of 'copy_0' at 7:7
|]



    describe "reduced copy constraint" $ do

      let program = [r|
datatype boxed Boxed a = Boxed a

copy : forall a | Copy a . Boxed a -> (Boxed a, Boxed a)
copy x = (x, x)
|]

      it "does not type check" $ check program  `shouldReturn` trim [r|
type check error: unable to satisfy: Copy Boxed a_1
  | primary cause: variable 'x_0' used more than once at 5:14
  | secondary cause: function signature for 'copy_0' at 4:1
|]





  describe "unboxed type" $ do

    describe "no copy constraint" $ do

      let program = [r|
datatype unboxed Unboxed [a, b] = Unboxed (a, b)

copy : forall a b . Unboxed [a, b] -> (Unboxed [a, b], Unboxed [a, b])
copy x =  (x, x)
|]

      it "does not type check" $ check program  `shouldReturn` trim [r|
type check error: unable to satisfy: Copy Unboxed [ a_1 , b_1 ]
  | primary cause: variable 'x_0' used more than once at 5:15
  | secondary cause: function signature for 'copy_0' at 4:1
|]



    describe "trivial copy constraint" $ do

      let program = [r|
datatype unboxed Unboxed [a, b] = Unboxed (a, b)

copy : forall a b | Copy Unboxed [a, b] . Unboxed [a, b] -> (Unboxed [a, b], Unboxed [a, b])
copy x = (x, x)

foo = copy (Unboxed (1, 'c'))
|]

      it "type checks" $ check program `shouldReturn` trim [r|
datatype unboxed Unboxed [ a_0 , b_0 ] = [forall a_0 b_0 . ( a_0 , b_0 ) -> Unboxed [ a_0 , b_0 ]] Unboxed ( a_0 , b_0 )
copy_0 : forall a_1 b_1 | Copy Unboxed [ a_1 , b_1 ] . Unboxed [ a_1 , b_1 ] -> ( Unboxed [ a_1 , b_1 ] , Unboxed [ a_1 , b_1 ] ) = \ [Unboxed [ a_1 , b_1 ]] x_0 -> ( [Unboxed [ a_1 , b_1 ]] x_0 , [Unboxed [ a_1 , b_1 ]] x_0 )
foo_0 = [Unboxed [ I32 , Char ] -> ( Unboxed [ I32 , Char ] , Unboxed [ I32 , Char ] )] copy_0 [( I32 , Char ) -> Unboxed [ I32 , Char ]] Unboxed ( [I32] 1 , [Char] 'c' )
|]



    describe "reduced copy constraint" $ do

      let program = [r|
datatype unboxed Unboxed [a, b] = Unboxed (a, b)

copy : forall a b | Copy a, Copy b . Unboxed [a, b] -> (Unboxed [a, b], Unboxed [a, b])
copy x = (x, x)

foo = copy (Unboxed (1, 'c'))
|]

      it "type checks" $ check program `shouldReturn` trim [r|
datatype unboxed Unboxed [ a_0 , b_0 ] = [forall a_0 b_0 . ( a_0 , b_0 ) -> Unboxed [ a_0 , b_0 ]] Unboxed ( a_0 , b_0 )
copy_0 : forall a_1 b_1 | Copy a_1 , Copy b_1 . Unboxed [ a_1 , b_1 ] -> ( Unboxed [ a_1 , b_1 ] , Unboxed [ a_1 , b_1 ] ) = \ [Unboxed [ a_1 , b_1 ]] x_0 -> ( [Unboxed [ a_1 , b_1 ]] x_0 , [Unboxed [ a_1 , b_1 ]] x_0 )
foo_0 = [Unboxed [ I32 , Char ] -> ( Unboxed [ I32 , Char ] , Unboxed [ I32 , Char ] )] copy_0 [( I32 , Char ) -> Unboxed [ I32 , Char ]] Unboxed ( [I32] 1 , [Char] 'c' )
|]

