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
datatype unboxed Fun [ a_0 , b_0 ] = Fun ( a_0 -> b_0 )
unbox_fun_0 : forall a_1 b_1 . Fun [ a_1 , b_1 ] -> a_1 -> b_1 = \ Fun f_0 -> \ x_0 -> f_0 x_0
id_fun_0 : forall a_2 . ( ) -> Fun [ a_2 , a_2 ] = \ ( ) -> Fun ( \ x_1 -> x_1 )
|]

    it "type checks" $ check program `shouldReturn` trim [r|
datatype unboxed Fun [ a_0 , b_0 ] = [forall a_0 b_0 . ( a_0 -> b_0 ) -> Fun [ a_0 , b_0 ]] Fun ( a_0 -> b_0 )
unbox_fun_0 : forall a_1 b_1 . Fun [ a_1 , b_1 ] -> a_1 -> b_1 = \ [Fun [ a_1 , b_1 ]] Fun [a_1 -> b_1] f_0 -> \ [a_1] x_0 -> [a_1 -> b_1] f_0 [a_1] x_0
id_fun_0 : forall a_2 . ( ) -> Fun [ a_2 , a_2 ] = \ [( )] ( ) -> [( a_2 -> a_2 ) -> Fun [ a_2 , a_2 ]] Fun ( \ [a_2] x_1 -> [a_2] x_1 )
|]

    it "evaluates" $ interpret program "(unbox_fun id_fun ()) 4"  `shouldReturn` "4"



  describe "datatype Unboxed (unboxed)" $ do

    let program = [r|
datatype unboxed Unboxed a = Unboxed a
|]

    it "type checks" $ check program `shouldReturn` trim [r|
datatype unboxed Unboxed a_0 = [forall a_0 . a_0 -> Unboxed a_0] Unboxed a_0
|]

    it "translates" $ translate program `shouldReturn` trim [r|
template<typename a_0>
struct Unboxed : std::variant<a_0> {
  using std::variant<a_0>::variant;
  template<size_t index>
  inline const auto& get() const { return std::get<index>(*this); }
  template<size_t index>
  inline auto& get() { return std::get<index>(*this); }
};
static constexpr size_t _idxUnboxed = 0;
auto _conUnboxed = []<typename a_0>(){
  return std::function([](a_0&& arg) -> Unboxed<a_0> {
    return Unboxed<a_0>(std::in_place_index<_idxUnboxed>, std::move(arg));
  });
};
|]


  describe "datatype Boxed (boxed)" $ do

    let program = [r|
datatype boxed Boxed a = Boxed a
|]

    it "type checks" $ check program `shouldReturn` trim [r|
datatype boxed Boxed a_0 = [forall a_0 . a_0 -> Boxed a_0] Boxed a_0
|]

    it "translates" $ translate program `shouldReturn` trim [r|
template<typename a_0>
struct _implBoxed;
template<typename a_0>
using Boxed = praxis::Boxed<_implBoxed<a_0>>;
template<typename a_0>
struct _implBoxed : std::variant<a_0> {
  using std::variant<a_0>::variant;
  template<size_t index>
  inline const auto& get() const { return std::get<index>(*this); }
  template<size_t index>
  inline auto& get() { return std::get<index>(*this); }
};
static constexpr size_t _idxBoxed = 0;
auto _conBoxed = []<typename a_0>(){
  return std::function([](a_0&& arg) -> Boxed<a_0> {
    return praxis::mkBoxed<_implBoxed<a_0>>(std::in_place_index<_idxBoxed>, std::move(arg));
  });
};
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
  sum : forall &r. &r List Int -> Int
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
  sum_0 : forall & r_0 . & r_0 List Int -> Int = cases
    Nil ( ) -> 0
    Cons ( x_1 , xs_1 ) -> add_int ( x_1 , sum_0 xs_1 )
|]

    it "type checks" $ check program `shouldReturn` trim [r|
datatype rec List a_0 = [forall a_0 . ( ) -> List a_0] Nil ( ) | [forall a_0 . ( a_0 , List a_0 ) -> List a_0] Cons ( a_0 , List a_0 )
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
struct _implList;
template<typename a_0>
using List = praxis::Boxed<_implList<a_0>>;
template<typename a_0>
struct _implList : std::variant<std::monostate, std::pair<a_0, List<a_0>>> {
  using std::variant<std::monostate, std::pair<a_0, List<a_0>>>::variant;
  template<size_t index>
  inline const auto& get() const { return std::get<index>(*this); }
  template<size_t index>
  inline auto& get() { return std::get<index>(*this); }
};
static constexpr size_t _idxNil = 0;
static constexpr size_t _idxCons = 1;
auto _conNil = []<typename a_0>(){
  return std::function([](std::monostate&& arg) -> List<a_0> {
    return praxis::mkBoxed<_implList<a_0>>(std::in_place_index<_idxNil>, std::move(arg));
  });
};
auto _conCons = []<typename a_0>(){
  return std::function([](std::pair<a_0, List<a_0>>&& arg) -> List<a_0> {
    return praxis::mkBoxed<_implList<a_0>>(std::in_place_index<_idxCons>, std::move(arg));
  });
};
auto _temp_0 = [](auto _temp_1){
  return std::tuple{
    /* 4:1 */
    [&]<praxis::View v_0, typename a_1, typename b_0>(){
      return std::function([&](std::function<b_0(praxis::apply<v_0, a_1>)> _temp_2){
        auto [map_0] = _temp_1(_temp_1);
        auto f_0 = std::move(_temp_2);
        return std::function([&](praxis::apply<v_0, List<a_1>> _temp_3){
          if (_temp_3.index() == _idxNil) {
            auto _temp_4 = _temp_3.template get<_idxNil>();
            return _conNil.template operator()<b_0>()(std::monostate{});
          }
          if (_temp_3.index() == _idxCons) {
            auto _temp_5 = _temp_3.template get<_idxCons>();
            auto _temp_6 = praxis::first(_temp_5);
            auto _temp_7 = praxis::second(_temp_5);
            auto x_0 = std::move(_temp_6);
            auto xs_0 = std::move(_temp_7);
            return _conCons.template operator()<b_0>()(std::make_pair(std::move(f_0)(std::move(x_0)), std::move(map_0).template operator()<v_0, a_1, b_0>()(std::move(f_0))(std::move(xs_0))));
          }
          throw praxis::CaseFail("6:11");
        });
        throw praxis::BindFail("6:7");
      });
    }
  };
};
auto [map_0] = _temp_0(_temp_0);
auto _temp_8 = [](auto _temp_9) -> std::tuple<std::function<int(praxis::apply<praxis::View::REF, List<int>>)>> {
  return std::tuple{
    /* 10:1 */
    std::function([&](praxis::apply<praxis::View::REF, List<int>> _temp_10){
      auto [sum_0] = _temp_9(_temp_9);
      if (_temp_10.index() == _idxNil) {
        auto _temp_11 = _temp_10.template get<_idxNil>();
        return 0;
      }
      if (_temp_10.index() == _idxCons) {
        auto _temp_12 = _temp_10.template get<_idxCons>();
        auto _temp_13 = praxis::first(_temp_12);
        auto _temp_14 = praxis::second(_temp_12);
        auto x_1 = std::move(_temp_13);
        auto xs_1 = std::move(_temp_14);
        return std::move(add_int)(std::make_pair(std::move(x_1), std::move(sum_0)(std::move(xs_1))));
      }
      throw praxis::CaseFail("12:9");
    })
  };
};
auto [sum_0] = _temp_8(_temp_8);
|]

    it "compiles" $ compile program `shouldReturn` True

    it "runs" $ compileAndRun program "let xs = Cons (1, Cons (2, Cons (3, Nil ()))) in sum &xs" `shouldReturn` "6"

