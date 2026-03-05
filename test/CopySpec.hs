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
copy : forall a | Copy ( a , a ) . a -> ( a , a ) = \ [a] x -> ( [a] x , [a] x )
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
f : forall &r a . &r a -> ( &r a , &r a ) = \ [&r a] x -> ( [&r a] x , [&r a] x )
|]


  describe "generic views" $ do

    describe "can be copied if the underlying type can be copied" $ do

      let program = [r|
f : forall ?r a | Copy a . ?r a -> (?r a, ?r a)
f x = (x, x)
|]

      it "type checks" $ runPretty (check ProgramT program) `shouldReturn` trim [r|
f : forall ?r a | Copy a . a -> ( a , a ) = \ [a] x -> ( [a] x , [a] x )
|]

    describe "can not be copied if the underlying type can not be copied" $ do

      let program = [r|
f : forall ?r a. ?r a -> (?r a, ?r a)
f x = (x, x)
|]

      it "does not type check" $ runPretty (check ProgramT program) `shouldReturn` trim [r|
type check error: unable to satisfy: Copy a
  | derived from: Copy ( ?r a )
  | primary cause: variable x used more than once at 3:11
  | secondary cause: function f with signature forall ?r a . ?r a -> ( ?r a , ?r a ) at 2:1
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
type check error: unable to satisfy: Copy ( Boxed a )
  | primary cause: variable x used more than once at 5:14
  | secondary cause: function copy with signature forall a . Boxed a -> ( Boxed a , Boxed a ) at 4:1
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
type check error: unable to satisfy: Copy ( Boxed a )
  | primary cause: variable x used more than once at 5:14
  | secondary cause: function copy with signature forall a | Copy a . Boxed a -> ( Boxed a , Boxed a ) at 4:1
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
type check error: unable to satisfy: Copy a
  | derived from: Copy ( Unboxed a b )
  | primary cause: variable x used more than once at 5:15
  | secondary cause: function copy with signature forall a b . Unboxed a b -> ( Unboxed a b , Unboxed a b ) at 4:1
|]

      describe "trivial copy constraint" $ do

        let program = [r|
datatype unboxed Unboxed a b = Unboxed (a, b)

copy : forall a b | Copy (Unboxed a b) . Unboxed a b -> (Unboxed a b, Unboxed a b)
copy x = (x, x)

foo = copy (Unboxed (1, 'c'))
|]

        it "type checks" $ runPretty (check ProgramT program) `shouldReturn` trim [r|
datatype unboxed Unboxed a b = [forall a b . ( a , b ) -> Unboxed a b] Unboxed ( a , b )
copy : forall a b | Copy ( Unboxed a b ) . Unboxed a b -> ( Unboxed a b , Unboxed a b ) = \ [Unboxed a b] x -> ( [Unboxed a b] x , [Unboxed a b] x )
foo = [Unboxed I32 Char -> ( Unboxed I32 Char , Unboxed I32 Char )] copy ( [( I32 , Char ) -> Unboxed I32 Char] Unboxed ( [I32] 1 , [Char] 'c' ) )
|]

      describe "reduced copy constraint" $ do

        let program = [r|
datatype unboxed Unboxed a b = Unboxed (a, b)

copy : forall a b | Copy a, Copy b . Unboxed a b -> (Unboxed a b, Unboxed a b)
copy x = (x, x)

foo = copy (Unboxed (1, 'c'))
|]

        it "type checks" $ runPretty (check ProgramT program) `shouldReturn` trim [r|
datatype unboxed Unboxed a b = [forall a b . ( a , b ) -> Unboxed a b] Unboxed ( a , b )
copy : forall a b | Copy a , Copy b . Unboxed a b -> ( Unboxed a b , Unboxed a b ) = \ [Unboxed a b] x -> ( [Unboxed a b] x , [Unboxed a b] x )
foo = [Unboxed I32 Char -> ( Unboxed I32 Char , Unboxed I32 Char )] copy ( [( I32 , Char ) -> Unboxed I32 Char] Unboxed ( [I32] 1 , [Char] 'c' ) )
|]
