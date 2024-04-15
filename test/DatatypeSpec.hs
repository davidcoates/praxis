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
datatype Either [ a_0 , b_0 ] = Left a_0 | Right b_0
|]

    it "type checks" $ check program `shouldReturn` trim [r|
datatype Either [ a_0 , b_0 ] = [forall a_0 b_0 . a_0 -> Either [ a_0 , b_0 ]] Left a_0 | [forall a_0 b_0 . b_0 -> Either [ a_0 , b_0 ]] Right b_0
|]

    it "evaluates" $ do
      interpret program "Left 0 : Either [Int, ()]"  `shouldReturn` "Left 0"
      interpret program "Right 1 : Either [(), Int]" `shouldReturn` "Right 1"



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
datatype Fun [ a_0 , b_0 ] = Fun ( a_0 -> b_0 )
unbox_fun_0 : forall a_1 b_1 . Fun [ a_1 , b_1 ] -> a_1 -> b_1 = \ Fun f_0 -> \ x_0 -> f_0 x_0
id_fun_0 : forall a_2 . ( ) -> Fun [ a_2 , a_2 ] = \ ( ) -> Fun ( \ x_1 -> x_1 )
|]

    it "type checks" $ check program `shouldReturn` trim [r|
datatype Fun [ a_0 , b_0 ] = [forall a_0 b_0 . ( a_0 -> b_0 ) -> Fun [ a_0 , b_0 ]] Fun ( a_0 -> b_0 )
unbox_fun_0 : forall a_1 b_1 . Fun [ a_1 , b_1 ] -> a_1 -> b_1 = \ [Fun [ a_1 , b_1 ]] Fun [a_1 -> b_1] f_0 -> \ [a_1] x_0 -> [a_1 -> b_1] f_0 [a_1] x_0
id_fun_0 : forall a_2 . ( ) -> Fun [ a_2 , a_2 ] = \ [( )] ( ) -> [( a_2 -> a_2 ) -> Fun [ a_2 , a_2 ]] Fun ( \ [a_2] x_1 -> [a_2] x_1 )
|]

    it "evaluates" $ interpret program "(unbox_fun id_fun ()) 4"  `shouldReturn` "4"



  describe "datatype List (with map & sum)" $ do

    let program = [r|
datatype List a = Nil () | Cons (a, List a)

rec
  map : forall ?v a b. (?v a -> b) -> ?v List a -> List b
  map f = cases
    Nil ()       -> Nil ()
    Cons (x, xs) -> Cons (f x, (map f) xs)

rec
  sum : forall &r. &r List Int -> Int
  sum = cases
    Nil ()       -> 0
    Cons (x, xs) -> x + sum xs
|]

    it "parses" $ parse program `shouldReturn` trim [r|
datatype List a_0 = Nil ( ) | Cons ( a_0 , List a_0 )
rec
  map_0 : forall ? v_0 a_1 b_0 . ( ? v_0 a_1 -> b_0 ) -> ? v_0 List a_1 -> List b_0 = \ f_0 -> cases
    Nil ( ) -> Nil ( )
    Cons ( x_0 , xs_0 ) -> Cons ( f_0 x_0 , ( map_0 f_0 ) xs_0 )
rec
  sum_0 : forall & r_0 . & r_0 List Int -> Int = cases
    Nil ( ) -> 0
    Cons ( x_1 , xs_1 ) -> add_int ( x_1 , sum_0 xs_1 )
|]

    it "type checks" $ check program `shouldReturn` trim [r|
datatype List a_0 = [forall a_0 . ( ) -> List a_0] Nil ( ) | [forall a_0 . ( a_0 , List a_0 ) -> List a_0] Cons ( a_0 , List a_0 )
rec
  map_0 : forall ? v_0 a_1 b_0 . ( ? v_0 a_1 -> b_0 ) -> ? v_0 List a_1 -> List b_0 = \ [? v_0 a_1 -> b_0] f_0 -> [? v_0 List a_1 -> List b_0] cases
    [? v_0 List a_1] Nil [( )] ( ) -> [( ) -> List b_0] Nil [( )] ( )
    [? v_0 List a_1] Cons ( [? v_0 a_1] x_0 , [? v_0 List a_1] xs_0 ) -> [( b_0 , List b_0 ) -> List b_0] Cons ( [? v_0 a_1 -> b_0] f_0 [? v_0 a_1] x_0 , ( [( ? v_0 a_1 -> b_0 ) -> ? v_0 List a_1 -> List b_0] map_0 [? v_0 a_1 -> b_0] f_0 ) [? v_0 List a_1] xs_0 )
rec
  sum_0 : forall & r_0 . & r_0 List Int -> Int = [& r_0 List Int -> Int] cases
    [& r_0 List Int] Nil [( )] ( ) -> [Int] 0
    [& r_0 List Int] Cons ( [Int] x_1 , [& r_0 List Int] xs_1 ) -> [( Int , Int ) -> Int] add_int ( [Int] x_1 , [& r_0 List Int -> Int] sum_0 [& r_0 List Int] xs_1 )
|]

    it "evaluates" $ do

      interpret program [r|
do
  let xs = Cons (1, Cons (2, Cons (3, Nil ())))
  sum &xs
|] `shouldReturn` "6"

      interpret program [r|
do
  let xs = Cons (1, Cons (2, Cons (3, Nil ())))
  let ys = (map (\x -> x * 2)) &xs
  sum &ys
|] `shouldReturn` "12"


    it "translates" $ translate program `shouldReturn` trim [r|
template<typename a_0>
struct ListImpl;
template<typename a_0>
using List = praxis::Box<ListImpl<a_0>>;
template<typename a_0>
struct ListImpl : std::variant<std::monostate, std::pair<a_0, List<a_0>>> {
  using std::variant<std::monostate, std::pair<a_0, List<a_0>>>::variant;
  template<size_t index>
  inline const auto& get() const { return std::get<index>(*this); }
  template<size_t index>
  inline auto& get() { return std::get<index>(*this); }
};
static constexpr size_t Nil = 0;
static constexpr size_t Cons = 1;
auto mkNil = []<typename a_0>(){
  return std::function([](std::monostate&& arg) -> List<a_0> {
    return praxis::mkBox<ListImpl<a_0>>(std::in_place_index<Nil>, std::move(arg));
  });
};
auto mkCons = []<typename a_0>(){
  return std::function([](std::pair<a_0, List<a_0>>&& arg) -> List<a_0> {
    return praxis::mkBox<ListImpl<a_0>>(std::in_place_index<Cons>, std::move(arg));
  });
};
auto temp_0_ = [](auto temp_1_){
  return std::tuple{
    /* 4:1 */
    [&]<praxis::View v_0, typename a_1, typename b_0>(){
      return std::function([&](std::function<b_0(praxis::apply<v_0, a_1>)> temp_2_){
        auto [map_0] = temp_1_(temp_1_);
        auto f_0 = std::move(temp_2_);
        return std::function([&](praxis::apply<v_0, List<a_1>> temp_3_){
          if (temp_3_.index() == Nil) {
            auto temp_4_ = temp_3_.template get<Nil>();
            return mkNil.template operator()<b_0>()(std::monostate{});
          }
          if (temp_3_.index() == Cons) {
            auto temp_5_ = temp_3_.template get<Cons>();
            auto temp_6_ = praxis::first(temp_5_);
            auto temp_7_ = praxis::second(temp_5_);
            auto x_0 = std::move(temp_6_);
            auto xs_0 = std::move(temp_7_);
            return mkCons.template operator()<b_0>()(std::make_pair(std::move(f_0)(std::move(x_0)), std::move(map_0).template operator()<v_0, a_1, b_0>()(std::move(f_0))(std::move(xs_0))));
          }
          throw praxis::CaseFail("6:11");
        });
        throw praxis::BindFail("6:7");
      });
    }
  };
};
auto [map_0] = temp_0_(temp_0_);
auto temp_8_ = [](auto temp_9_) -> std::tuple<std::function<int(praxis::apply<praxis::View::REF, List<int>>)>> {
  return std::tuple{
    /* 10:1 */
    std::function([&](praxis::apply<praxis::View::REF, List<int>> temp_10_){
      auto [sum_0] = temp_9_(temp_9_);
      if (temp_10_.index() == Nil) {
        auto temp_11_ = temp_10_.template get<Nil>();
        return 0;
      }
      if (temp_10_.index() == Cons) {
        auto temp_12_ = temp_10_.template get<Cons>();
        auto temp_13_ = praxis::first(temp_12_);
        auto temp_14_ = praxis::second(temp_12_);
        auto x_1 = std::move(temp_13_);
        auto xs_1 = std::move(temp_14_);
        return std::move(add_int)(std::make_pair(std::move(x_1), std::move(sum_0)(std::move(xs_1))));
      }
      throw praxis::CaseFail("12:9");
    })
  };
};
auto [sum_0] = temp_8_(temp_8_);
|]

    it "compiles" $ compile program `shouldReturn` True

    it "runs" $ compileAndRun program "let xs = Cons (1, Cons (2, Cons (3, Nil ()))) in sum &xs" `shouldReturn` "6"

