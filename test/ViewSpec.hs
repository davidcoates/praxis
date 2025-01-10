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

    it "parses" $ runPretty (parse ProgramT program) `shouldReturn` trim [r|
view : forall ?v a b . ?v ( a , b ) -> ( ?v b , ?v a ) = \ ( x , y ) -> ( y , x )
|]

    it "type checks" $ runPretty (check ProgramT program) `shouldReturn` trim [r|
view_0 : forall ?v_0 a_0 b_0 . ?v_0 ( a_0 , b_0 ) -> ( ?v_0 b_0 , ?v_0 a_0 ) = \ ( [?v_0 a_0] x_0 , [?v_0 b_0] y_0 ) -> ( [?v_0 b_0] y_0 , [?v_0 a_0] x_0 )
|]


  describe "boxed references" $ do

    let program = trim [r|
datatype Box &v !a = Box &v !a

rec datatype List a = Nil () | Cons (a, List a)

box = Box "x"
|]

    it "parses" $ runPretty (parse ProgramT program) `shouldReturn` trim [r|
datatype unboxed Box &v !a = Box &v !a
rec
  datatype boxed List a = Nil ( ) | Cons ( a , List a )
box = Box "x"
|]

    it "type checks" $ runPretty (check ProgramT program) `shouldReturn` trim [r|
datatype unboxed Box &v_0 !a_0 = [forall &v_0 !a_0 . &v_0 !a_0 -> Box &v_0 !a_0] Box &v_0 !a_0
rec
  datatype boxed List a_1 = [forall a_1 . ( ) -> List a_1] Nil ( ) | [forall a_1 . ( a_1 , List a_1 ) -> List a_1] Cons ( a_1 , List a_1 )
box_0 = [&'l0 String -> Box &'l0 String] Box [&'l0 String] "x"
|]

    -- TODO should also try with ? instead of &
    describe "construct with non-reference" $

      it "does not type check" $ do
        runPretty (check ProgramT program >> check ExpT "let xs = Cons (1, Cons (2, Cons (3, Nil ()))) in Box xs") `shouldReturn` trim [r|
type check error: unable to satisfy: Ref @
  | derived from: List ^t2 = List ^t2
  | primary cause: binding [List ^t2] xs_0 (<-) [( ^t2 , List ^t2 ) -> List ^t2] Cons ( [^t2] 1 , [( ^t2 , List ^t2 ) -> List ^t2] Cons ( [^t2] 2 , [( ^t2 , List ^t2 ) -> List ^t2] Cons ( [^t2] 3 , [( ) -> List ^t2] Nil [( )] ( ) ) ) ) at 1:5
  | secondary causes:
  | - application [List ^t2 -> Box @ ( List ^t2 )] Box ($) [List ^t2] xs_0 at 1:50
  | - application [( ^t2 , List ^t2 ) -> List ^t2] Cons ($) ( [^t2] 1 , [( ^t2 , List ^t2 ) -> List ^t2] Cons ( [^t2] 2 , [( ^t2 , List ^t2 ) -> List ^t2] Cons ( [^t2] 3 , [( ) -> List ^t2] Nil [( )] ( ) ) ) ) at 1:10
|]

    describe "construct with reference" $

      it "type checks" $ do
        runPretty (check ProgramT program >> check ExpT [r|
do
  let xs = Cons (1, Cons (2, Cons (3, Nil ())))
  read xs in do
    Box xs
    () -- Note, Box xs can't escape the read
|]) `shouldReturn` "[( )] let [List I32] xs_0 = [( I32 , List I32 ) -> List I32] Cons ( [I32] 1 , [( I32 , List I32 ) -> List I32] Cons ( [I32] 2 , [( I32 , List I32 ) -> List I32] Cons ( [I32] 3 , [( ) -> List I32] Nil [( )] ( ) ) ) ) in read xs_0 in [( )] [&'l1 List I32 -> Box &'l1 ( List I32 )] Box [&'l1 List I32] xs_0 seq [( )] ( )"


  describe "read safety" $ do

    let program = trim [r|
rec datatype List a = Nil () | Cons (a, List a)

x = Cons (1, Cons (2, Cons (3, Nil ())))

y = read x in (1, x)

|]

    it "parses" $ runPretty (parse ProgramT program) `shouldReturn` trim [r|
rec
  datatype boxed List a = Nil ( ) | Cons ( a , List a )
x = Cons ( 1 , Cons ( 2 , Cons ( 3 , Nil ( ) ) ) )
y = read x in ( 1 , x )
|]

    it "does not type check" $ runPretty (check ProgramT program) `shouldReturn` trim [r|
type check error: unable to satisfy: 'l0 ∉ ( I32 , &'l0 List I32 )
  | primary cause: read of x at 5:5
  | secondary causes:
  | - application [( I32 , List I32 ) -> List I32] Cons ($) ( [I32] 1 , [( I32 , List I32 ) -> List I32] Cons ( [I32] 2 , [( I32 , List I32 ) -> List I32] Cons ( [I32] 3 , [( ) -> List I32] Nil [( )] ( ) ) ) ) at 3:5
  | - integer literal 1 at 3:11
  | - integer literal 1 at 5:16
|]
