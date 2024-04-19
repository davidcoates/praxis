{-# LANGUAGE QuasiQuotes #-}

module ViewSpec where

import           Test.Hspec
import           Text.RawString.QQ

import           Util


spec :: Spec
spec = do

  describe "polymorphic view pattern match (pair decomposition)" $ do

    let program = [r|
view : forall ?v a b. ?v (a, b) -> (?v b, ?v a)
view (x, y) = (y, x)
|]

    it "parses" $ parse program `shouldReturn` trim [r|
view_0 : forall ? v_0 a_0 b_0 . ? v_0 ( a_0 , b_0 ) -> ( ? v_0 b_0 , ? v_0 a_0 ) = \ ( x_0 , y_0 ) -> ( y_0 , x_0 )
|]

    it "type checks" $ check program `shouldReturn` trim [r|
view_0 : forall ? v_0 a_0 b_0 . ? v_0 ( a_0 , b_0 ) -> ( ? v_0 b_0 , ? v_0 a_0 ) = \ ( [? v_0 a_0] x_0 , [? v_0 b_0] y_0 ) -> ( [? v_0 b_0] y_0 , [? v_0 a_0] x_0 )
|]

    it "translates" $ translate program `shouldReturn` trim [r|
/* 2:1 */
auto view_0 = []<praxis::View v_0, typename a_0, typename b_0>(){
  return std::function([&](praxis::apply<v_0, std::pair<a_0, b_0>> _temp_0){
    auto _temp_1 = praxis::first(_temp_0);
    auto _temp_2 = praxis::second(_temp_0);
    auto x_0 = std::move(_temp_1);
    auto y_0 = std::move(_temp_2);
    return std::make_pair(std::move(y_0), std::move(x_0));
    throw praxis::BindFail("3:6");
  });
};
|]

    it "compiles" $ compile program `shouldReturn` True



  describe "boxed references" $ do

    let program = trim [r|
datatype Box [&v, a] = Box &v a

datatype rec List a = Nil () | Cons (a, List a)

box = Box "x"
|]

    it "parses" $ parse program `shouldReturn` trim [r|
datatype unboxed Box [ & v_0 , a_0 ] = Box & v_0 a_0
datatype rec List a_1 = Nil ( ) | Cons ( a_1 , List a_1 )
box_0 = Box "x"
|]

    it "type checks" $ check program `shouldReturn` trim [r|
datatype unboxed Box [ & v_0 , a_0 ] = [forall & v_0 a_0 . & v_0 a_0 -> Box [ & v_0 , a_0 ]] Box & v_0 a_0
datatype rec List a_1 = [forall a_1 . ( ) -> List a_1] Nil ( ) | [forall a_1 . ( a_1 , List a_1 ) -> List a_1] Cons ( a_1 , List a_1 )
box_0 = [& 'l0 String -> Box [ & 'l0 , String ]] Box [& 'l0 String] "x"
|]

    -- TODO should also try with ? instead of &
    it "evaluates" $ do

      interpret program "let xs = Cons (1, Cons (2, Cons (3, Nil ()))) in Box xs" `shouldReturn` trim [r|
type check error: unable to satisfy: & ^v3 List Int ?= List Int
  | derived from: ( Int , List Int ) -> List Int = ( Int , List Int ) -> & ^v3 List Int
  | primary cause: application [( Int , List Int ) -> List Int] Cons ($) ( [Int] 1 , [( ^t5 , List ^t5 ) -> List ^t5] Cons ( [Int] 2 , [( ^t7 , List ^t7 ) -> List ^t7] Cons ( [Int] 3 , [( ) -> List ^t9] Nil [( )] ( ) ) ) ) at 1:10
  | secondary causes:
  | - binding [& ^v3 List Int] xs_0 (<-) [( Int , List Int ) -> List Int] Cons ( [Int] 1 , [( ^t5 , List ^t5 ) -> List ^t5] Cons ( [Int] 2 , [( ^t7 , List ^t7 ) -> List ^t7] Cons ( [Int] 3 , [( ) -> List ^t9] Nil [( )] ( ) ) ) ) at 1:5
  | - application [& ^v3 List Int -> Box [ & ^v3 , List Int ]] Box ($) [& ^v3 List Int] xs_0 at 1:50
|]

      interpret program [r|
do
  let xs = Cons (1, Cons (2, Cons (3, Nil ())))
  read xs in do
    Box xs
    () -- Note, Box xs can't escape the read
|] `shouldReturn` "()"



  describe "read safety" $ do

    let program = trim [r|
datatype rec List a = Nil () | Cons (a, List a)

x = Cons (1, Cons (2, Cons (3, Nil ())))

y = read x in (1, x)

|]

    it "parses" $ parse program `shouldReturn` trim [r|
datatype rec List a_0 = Nil ( ) | Cons ( a_0 , List a_0 )
x_0 = Cons ( 1 , Cons ( 2 , Cons ( 3 , Nil ( ) ) ) )
y_0 = read x_0 in ( 1 , x_0 )
|]

    it "does not type check" $ check program `shouldReturn` trim [r|
type check error: unable to satisfy: 'l0 ref-free ( Int , & 'l0 ^t0 )
  | primary cause: read of x_0 at 5:5
|]
