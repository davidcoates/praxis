{-# LANGUAGE QuasiQuotes #-}

module CopySpec where

import           Test.Hspec
import           Text.RawString.QQ

import           Introspect
import           Util


spec :: Spec
spec = do

  describe "assumption reduction" $ do

    let program = [r|
copy : forall a | Copy (a, a). a -> (a, a)
copy x = (x, x)
|]

    it "type checks" $ runPretty (check ProgramT program) `shouldReturn` trim [r|
copy_0 : forall a_0 | Copy ( a_0 , a_0 ) . a_0 -> ( a_0 , a_0 ) = \ [a_0] x_0 -> ( [a_0] x_0 , [a_0] x_0 )
|]


  describe "redundant constraint" $ do

    let program = [r|
f : forall a | Copy I32. a -> a
f x = x
|]

    it "does not type check" $ runPretty (check ProgramT program) `shouldReturn` trim [r|
type check error at 2:16: redundant constraint: Copy I32
|]


  describe "reference views" $ do

    describe "can be copied" $ do

      let program = [r|
f : forall &r a. &r a -> (&r a, &r a)
f x = (x, x)
|]

      it "type checks" $ runPretty (check ProgramT program) `shouldReturn` trim [r|
f_0 : forall &r_0 a_0 . &r_0 a_0 -> ( &r_0 a_0 , &r_0 a_0 ) = \ [&r_0 a_0] x_0 -> ( [&r_0 a_0] x_0 , [&r_0 a_0] x_0 )
|]


  describe "generic views" $ do

    describe "can be copied if the underlying type can be copied" $ do

      let program = [r|
f : forall ?r a | Copy a . ?r a -> (?r a, ?r a)
f x = (x, x)
|]

      it "type checks" $ runPretty (check ProgramT program) `shouldReturn` trim [r|
f_0 : forall ?r_0 a_0 | Copy a_0 . a_0 -> ( a_0 , a_0 ) = \ [a_0] x_0 -> ( [a_0] x_0 , [a_0] x_0 )
|]

    describe "can not be copied if the underlying type can not be copied" $ do

      let program = [r|
f : forall ?r a. ?r a -> (?r a, ?r a)
f x = (x, x)
|]

      it "does not type check" $ runPretty (check ProgramT program) `shouldReturn` trim [r|
type check error: unable to satisfy: Copy a_0
  | derived from: Copy ( ?r_0 a_0 )
  | primary cause: variable x used more than once at 3:11
  | secondary cause: function f with signature forall ?r_0 a_0 . ?r_0 a_0 -> ( ?r_0 a_0 , ?r_0 a_0 ) at 2:1
|]

  describe "boxed type" $ do

    describe "can not be copied" $ do

      describe "no copy constraint" $ do

        let program = [r|
datatype boxed Boxed a = Boxed a

copy : forall a . Boxed a -> (Boxed a, Boxed a)
copy x = (x, x)
|]

        it "does not type check" $ runPretty (check ProgramT program) `shouldReturn` trim [r|
type check error: unable to satisfy: Copy ( Boxed a_1 )
  | primary cause: variable x used more than once at 5:14
  | secondary cause: function copy with signature forall a_1 . Boxed a_1 -> ( Boxed a_1 , Boxed a_1 ) at 4:1
|]

      describe "trivial copy constraint" $ do

        let program = [r|
datatype boxed Boxed a = Boxed a

copy : forall a | Copy (Boxed a) . Boxed a -> (Boxed a, Boxed a)
copy x = (x, x)

foo = copy (Boxed 1)
|]

        it "does not type check" $ runPretty (check ProgramT program)  `shouldReturn` trim [r|
type check error: unable to satisfy: Copy ( Boxed ^t2 )
  | primary cause: specialization of copy at 7:7
|]

      describe "reduced copy constraint" $ do

        let program = [r|
datatype boxed Boxed a = Boxed a

copy : forall a | Copy a . Boxed a -> (Boxed a, Boxed a)
copy x = (x, x)
|]

        it "does not type check" $ runPretty (check ProgramT program)  `shouldReturn` trim [r|
type check error: unable to satisfy: Copy ( Boxed a_1 )
  | primary cause: variable x used more than once at 5:14
  | secondary cause: function copy with signature forall a_1 | Copy a_1 . Boxed a_1 -> ( Boxed a_1 , Boxed a_1 ) at 4:1
|]

  describe "unboxed type" $ do

    describe "can be copied when components can be copied" $ do

      describe "no copy constraint" $ do

        let program = [r|
datatype unboxed Unboxed a b = Unboxed (a, b)

copy : forall a b . Unboxed a b -> (Unboxed a b, Unboxed a b)
copy x =  (x, x)
|]

        it "does not type check" $ runPretty (check ProgramT program)  `shouldReturn` trim [r|
type check error: unable to satisfy: Copy a_1
  | derived from: Copy ( Unboxed a_1 b_1 )
  | primary cause: variable x used more than once at 5:15
  | secondary cause: function copy with signature forall a_1 b_1 . Unboxed a_1 b_1 -> ( Unboxed a_1 b_1 , Unboxed a_1 b_1 ) at 4:1
|]

      describe "trivial copy constraint" $ do

        let program = [r|
datatype unboxed Unboxed a b = Unboxed (a, b)

copy : forall a b | Copy (Unboxed a b) . Unboxed a b -> (Unboxed a b, Unboxed a b)
copy x = (x, x)

foo = copy (Unboxed (1, 'c'))
|]

        it "type checks" $ runPretty (check ProgramT program) `shouldReturn` trim [r|
datatype unboxed Unboxed a_0 b_0 = [forall a_0 b_0 . ( a_0 , b_0 ) -> Unboxed a_0 b_0] Unboxed ( a_0 , b_0 )
copy_0 : forall a_1 b_1 | Copy ( Unboxed a_1 b_1 ) . Unboxed a_1 b_1 -> ( Unboxed a_1 b_1 , Unboxed a_1 b_1 ) = \ [Unboxed a_1 b_1] x_0 -> ( [Unboxed a_1 b_1] x_0 , [Unboxed a_1 b_1] x_0 )
foo_0 = [Unboxed I32 Char -> ( Unboxed I32 Char , Unboxed I32 Char )] copy_0 ( [( I32 , Char ) -> Unboxed I32 Char] Unboxed ( [I32] 1 , [Char] 'c' ) )
|]

      describe "reduced copy constraint" $ do

        let program = [r|
datatype unboxed Unboxed a b = Unboxed (a, b)

copy : forall a b | Copy a, Copy b . Unboxed a b -> (Unboxed a b, Unboxed a b)
copy x = (x, x)

foo = copy (Unboxed (1, 'c'))
|]

        it "type checks" $ runPretty (check ProgramT program) `shouldReturn` trim [r|
datatype unboxed Unboxed a_0 b_0 = [forall a_0 b_0 . ( a_0 , b_0 ) -> Unboxed a_0 b_0] Unboxed ( a_0 , b_0 )
copy_0 : forall a_1 b_1 | Copy a_1 , Copy b_1 . Unboxed a_1 b_1 -> ( Unboxed a_1 b_1 , Unboxed a_1 b_1 ) = \ [Unboxed a_1 b_1] x_0 -> ( [Unboxed a_1 b_1] x_0 , [Unboxed a_1 b_1] x_0 )
foo_0 = [Unboxed I32 Char -> ( Unboxed I32 Char , Unboxed I32 Char )] copy_0 ( [( I32 , Char ) -> Unboxed I32 Char] Unboxed ( [I32] 1 , [Char] 'c' ) )
|]
