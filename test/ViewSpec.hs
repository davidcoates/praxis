{-# LANGUAGE QuasiQuotes #-}

module ViewSpec where

import           Test.Hspec
import           Text.RawString.QQ

import           Introspect
import           Util


spec :: Spec
spec = do

  describe "polymorphic view pattern match (pair decomposition)" $ do

    let program = [r|
view : forall ?v a b. ?v (a, b) -> (?v b, ?v a)
view (x, y) = (y, x)
|]

    it "parses" $ runPretty (parse IProgram program) `shouldReturn` trim [r|
view : forall ? v a b . ? v ( a , b ) -> ( ? v b , ? v a ) = \ ( x , y ) -> ( y , x )
|]

    it "type checks" $ runPretty (check IProgram program) `shouldReturn` trim [r|
view_0 : forall ? v_0 a_0 b_0 . ? v_0 ( a_0 , b_0 ) -> ( ? v_0 b_0 , ? v_0 a_0 ) = \ ( [? v_0 a_0] x_0 , [? v_0 b_0] y_0 ) -> ( [? v_0 b_0] y_0 , [? v_0 a_0] x_0 )
|]


  describe "boxed references" $ do

    let program = trim [r|
datatype Box &v a = Box &v a

datatype rec List a = Nil () | Cons (a, List a)

box = Box "x"
|]

    it "parses" $ runPretty (parse IProgram program) `shouldReturn` trim [r|
datatype unboxed Box & v a = Box & v a
datatype rec List a = Nil ( ) | Cons ( a , List a )
box = Box "x"
|]

    it "type checks" $ runPretty (check IProgram program) `shouldReturn` trim [r|
datatype unboxed Box & v_0 a_0 = [forall & v_0 a_0 . & v_0 a_0 -> Box & v_0 a_0] Box & v_0 a_0
datatype rec List a_1 = [forall a_1 . ( ) -> List a_1] Nil ( ) | [forall a_1 . ( a_1 , List a_1 ) -> List a_1] Cons ( a_1 , List a_1 )
box_0 = [& 'l0 String -> Box & 'l0 String] Box [& 'l0 String] "x"
|]

    -- TODO should also try with ? instead of &
    describe "construct with non-reference" $

      it "does not type check" $ do
        runPretty (check IProgram program >> check IExp "let xs = Cons (1, Cons (2, Cons (3, Nil ()))) in Box xs") `shouldReturn` trim [r|
type check error: unable to satisfy: & ^v3 ( List ^t4 ) ?= List ^t4
  | derived from: ( ^t4 , List ^t4 ) -> List ^t4 = ( ^t4 , List ^t4 ) -> & ^v3 ( List ^t4 )
  | primary cause: application [( ^t4 , List ^t4 ) -> List ^t4] Cons ($) ( [^t4] 1 , [( ^t6 , List ^t6 ) -> List ^t6] Cons ( [^t7] 2 , [( ^t9 , List ^t9 ) -> List ^t9] Cons ( [^t10] 3 , [( ) -> List ^t12] Nil [( )] ( ) ) ) ) at 1:10
  | secondary causes:
  | - binding [& ^v3 ( List ^t4 )] xs_0 (<-) [( ^t4 , List ^t4 ) -> List ^t4] Cons ( [^t4] 1 , [( ^t6 , List ^t6 ) -> List ^t6] Cons ( [^t7] 2 , [( ^t9 , List ^t9 ) -> List ^t9] Cons ( [^t10] 3 , [( ) -> List ^t12] Nil [( )] ( ) ) ) ) at 1:5
  | - application [& ^v3 ( List ^t4 ) -> Box & ^v3 ( List ^t4 )] Box ($) [& ^v3 ( List ^t4 )] xs_0 at 1:50
|]

    describe "construct with reference" $

      it "type checks" $ do
        runPretty (check IProgram program >> check IExp [r|
do
  let xs = Cons (1, Cons (2, Cons (3, Nil ())))
  read xs in do
    Box xs
    () -- Note, Box xs can't escape the read
|]) `shouldReturn` "[( )] let [List I32] xs_0 = [( I32 , List I32 ) -> List I32] Cons ( [I32] 1 , [( I32 , List I32 ) -> List I32] Cons ( [I32] 2 , [( I32 , List I32 ) -> List I32] Cons ( [I32] 3 , [( ) -> List I32] Nil [( )] ( ) ) ) ) in read xs_0 in [( )] [& 'l1 ( List I32 ) -> Box & 'l1 ( List I32 )] Box [& 'l1 ( List I32 )] xs_0 seq [( )] ( )"


  describe "read safety" $ do

    let program = trim [r|
datatype rec List a = Nil () | Cons (a, List a)

x = Cons (1, Cons (2, Cons (3, Nil ())))

y = read x in (1, x)

|]

    it "parses" $ runPretty (parse IProgram program) `shouldReturn` trim [r|
datatype rec List a = Nil ( ) | Cons ( a , List a )
x = Cons ( 1 , Cons ( 2 , Cons ( 3 , Nil ( ) ) ) )
y = read x in ( 1 , x )
|]

    it "does not type check" $ runPretty (check IProgram program) `shouldReturn` trim [r|
type check error: unable to satisfy: 'l0 ∉ ( ^t11 , & 'l0 ^t0 )
  | primary cause: read of x_0 at 5:5
|]
