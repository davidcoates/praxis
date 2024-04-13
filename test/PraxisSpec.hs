{-# LANGUAGE QuasiQuotes #-}

module PraxisSpec where

import           Control.Monad     (forM_)
import           Prelude           hiding (either)
import           Test.Hspec
import           Text.RawString.QQ

import           Introspect
import           Util


doBlock = describe "do" $ do

  let program = [r|
foo = do
  let x = 1
  ()
  let y = 2
  x + y
|]

  it "parses" $ parse program `shouldReturn` trim [r|
foo_0 = let x_0 = 1 in ( ) seq let y_0 = 2 in add_int ( x_0 , y_0 )
|]

  it "type checks" $ check program `shouldReturn` trim [r|
foo_0 = [Int] let [Int] x_0 = [Int] 1 in [Int] [( )] ( ) seq [Int] let [Int] y_0 = [Int] 2 in [( Int , Int ) -> Int] add_int ( [Int] x_0 , [Int] y_0 )
|]

  it "translates" $ translate program `shouldReturn` trim [r|
/* 2:1 */
auto foo_0 = [](){
  auto temp_0_ = 1;
  auto x_0 = std::move(temp_0_);
  return (praxis::Unit{}, [=](){
    auto temp_1_ = 2;
    auto y_0 = std::move(temp_1_);
    return std::move(add_int)(praxis::mkPair(std::move(x_0), std::move(y_0)));
    throw praxis::BindFail("5:7");
  }());
  throw praxis::BindFail("3:7");
}();
|]

  it "compiles" $ compile program `shouldReturn` True

  it "runs" $ compileAndRun program "foo" `shouldReturn` "3"



tuple = describe "tuple" $ do

  let program = "x = (1, True, \"abc\")"
  it "parses" $ parse program `shouldReturn` trim [r|
x_0 = ( 1 , True , "abc" )
|]

  it "type checks" $ check program `shouldReturn` trim [r|
x_0 = ( [Int] 1 , [Bool] True , [& 'l0 String] "abc" )
|]

  it "translates" $ translate program `shouldReturn` trim [r|
/* 1:1 */
auto x_0 = praxis::mkPair(1, praxis::mkPair(true, "abc"));
|]

  it "compiles" $ compile program `shouldReturn` True



ifThenElse = describe "if then else (min)" $ do

  let program = "min (x, y) = if x < y then x else y"

  it "parses" $ parse program `shouldReturn` trim [r|
min_0 = \ ( x_0 , y_0 ) -> if lt_int ( x_0 , y_0 ) then x_0 else y_0
|]

  it "type checks" $ check program `shouldReturn` trim [r|
min_0 = \ ( [Int] x_0 , [Int] y_0 ) -> [Int] if [( Int , Int ) -> Bool] lt_int ( [Int] x_0 , [Int] y_0 ) then [Int] x_0 else [Int] y_0
|]

  it "evaluates" $ do
    interpret program "min (1, 2)" `shouldReturn` "1"
    interpret program "min (2, 1)" `shouldReturn` "1"
    interpret program "min (1, 1)" `shouldReturn` "1"

  it "translates" $ translate program `shouldReturn` trim [r|
/* 1:1 */
auto min_0 = std::function([](praxis::Pair<int, int> temp_0_){
  auto temp_1_ = temp_0_.first();
  auto temp_2_ = temp_0_.second();
  auto x_0 = std::move(temp_1_);
  auto y_0 = std::move(temp_2_);
  return (std::move(lt_int)(praxis::mkPair(std::move(x_0), std::move(y_0)))) ? (std::move(x_0)) : (std::move(y_0));
  throw praxis::BindFail("1:5");
});
|]

  it "compiles" $ compile program `shouldReturn` True

  it "runs" $ do
    compileAndRun program "min (1, 2)" `shouldReturn` "1"
    compileAndRun program "min (2, 1)" `shouldReturn` "1"
    compileAndRun program "min (1, 1)" `shouldReturn` "1"



switch = describe "switch (sign)" $ do

  let program = [r|
sign : Int -> Int
sign n = switch
  n  < 0 -> -1
  n == 0 ->  0
  n  > 0 -> +1
|]

  it "parses" $ parse program `shouldReturn` trim [r|
sign_0 : Int -> Int = \ n_0 -> switch
  lt_int ( n_0 , 0 ) -> negate_int 1
  eq_int ( n_0 , 0 ) -> 0
  gt_int ( n_0 , 0 ) -> unary_plus_int 1
|]

  it "type checks" $ check program `shouldReturn` trim [r|
sign_0 : Int -> Int = \ [Int] n_0 -> [Int] switch
  [( Int , Int ) -> Bool] lt_int ( [Int] n_0 , [Int] 0 ) -> [Int -> Int] negate_int [Int] 1
  [( Int , Int ) -> Bool] eq_int ( [Int] n_0 , [Int] 0 ) -> [Int] 0
  [( Int , Int ) -> Bool] gt_int ( [Int] n_0 , [Int] 0 ) -> [Int -> Int] unary_plus_int [Int] 1
|]

  it "evaluates" $ do
    interpret program "sign 0"    `shouldReturn` "0"
    interpret program "sign 10"   `shouldReturn` "1"
    interpret program "sign (-5)" `shouldReturn` "-1"
    interpret program "sign -5"   `shouldReturn` trim [r|
error: found contradiction [1:1] Int = Int -> Int and Int = Int
|-> [1:1] ( Int , Int ) = ( Int -> Int , Int ) and Int = ^t6
|-> [1:1] ( Int , Int ) -> Int = ( Int -> Int , Int ) -> ^t6
|-> (function application)
|]  -- Note: Parses as "sign - 5" (binary subtract)

  it "translates" $ translate program `shouldReturn` trim [r|
/* 2:1 */
auto sign_0 = std::function([](int temp_0_){
  auto n_0 = std::move(temp_0_);
  return [=](){
    if (std::move(lt_int)(praxis::mkPair(std::move(n_0), 0))) {
      return std::move(negate_int)(1);
    }
    if (std::move(eq_int)(praxis::mkPair(std::move(n_0), 0))) {
      return 0;
    }
    if (std::move(gt_int)(praxis::mkPair(std::move(n_0), 0))) {
      return std::move(unary_plus_int)(1);
    }
    throw praxis::SwitchFail("3:10");
  }();
  throw praxis::BindFail("3:6");
});
|]

  it "compiles" $ compile program `shouldReturn` True

  it "runs" $ do
    compileAndRun program "sign 0"    `shouldReturn` "0"
    compileAndRun program "sign 10"   `shouldReturn` "1"
    compileAndRun program "sign (-5)" `shouldReturn` "-1"



recursion = describe "recursion (factorial)" $ do

  let program = [r|
rec
  fac = cases
    0 -> 1
    n -> n * fac (n - 1)
|]

  it "parses" $ parse program `shouldReturn` trim [r|
rec
  fac_0 = cases
    0 -> 1
    n_0 -> multiply_int ( n_0 , fac_0 subtract_int ( n_0 , 1 ) )
|]

  it "type checks" $ check program `shouldReturn` trim [r|
rec
  fac_0 = [Int -> Int] cases
    [Int] 0 -> [Int] 1
    [Int] n_0 -> [( Int , Int ) -> Int] multiply_int ( [Int] n_0 , [Int -> Int] fac_0 [( Int , Int ) -> Int] subtract_int ( [Int] n_0 , [Int] 1 ) )
|]

  it "evaluates" $ do
    interpret program "fac 0"  `shouldReturn` "1"
    interpret program "fac 5"  `shouldReturn` "120"
    interpret program "fac 15" `shouldReturn` "1307674368000"

  it "translates" $ translate program `shouldReturn` trim [r|
auto temp_0_ = [](auto temp_1_) -> std::tuple<std::function<int(int)>> {
  return std::tuple{
    /* 2:1 */
    std::function([=](int temp_2_){
      auto [fac_0] = temp_1_(temp_1_);
      if (temp_2_ == 0) {
        return 1;
      }
      auto n_0 = std::move(temp_2_);
      return std::move(multiply_int)(praxis::mkPair(std::move(n_0), std::move(fac_0)(std::move(subtract_int)(praxis::mkPair(std::move(n_0), 1)))));
      throw praxis::CaseFail("3:9");
    })
  };
};
auto [fac_0] = temp_0_(temp_0_);
|]

  it "compiles" $ compile program `shouldReturn` True

  it "runs" $ do
    compileAndRun program "fac 0"  `shouldReturn` "1"
    compileAndRun program "fac 5"  `shouldReturn` "120"
    compileAndRun program "fac 15" `shouldReturn` "2004310016" -- overflow moment (TODO should use fixed width)



mixfix = describe "mixfix operators" $ do

  let program = [r|
implies : (Bool, Bool) -> Bool
implies (a, b) = b || !a

operator (_ --> _) = implies

iff : (Bool, Bool) -> Bool
iff (a, b) = (a && b) || (!a && !b)

operator (_ <-> _) = iff where
  precedence below (_ --> _)

ifthenelse : (Bool, Int, Int) -> Int
ifthenelse (c, a, b) = if c then a else b

operator (_ <?> _ <:> _) = ifthenelse where
  precedence below (_ <-> _)
|]

  it "parses" $ parse program `shouldReturn` trim [r|
implies_0 : ( Bool , Bool ) -> Bool = \ ( a_0 , b_0 ) -> or ( b_0 , not a_0 )
operator ( _ --> _ ) = implies_0
iff_0 : ( Bool , Bool ) -> Bool = \ ( a_1 , b_1 ) -> or ( and ( a_1 , b_1 ) , and ( not a_1 , not b_1 ) )
operator ( _ <-> _ ) = iff_0 where
  precedence
    below ( _ --> _ )
ifthenelse_0 : ( Bool , Int , Int ) -> Int = \ ( c_0 , a_2 , b_2 ) -> if c_0 then a_2 else b_2
operator ( _ <?> _ <:> _ ) = ifthenelse_0 where
  precedence
    below ( _ <-> _ )
|]

  it "evaluates" $ do
    interpret program "False <-> True <?> 1 <:> 0" `shouldReturn` "0"



unusedVar = describe "unused variables" $ do

  describe "unused variable" $ do

    let program = trim [r|
fst : forall a b. (a, b) -> a
fst (x, y) = x
|]

    it "parses" $ parse program `shouldReturn` trim [r|
fst_0 : forall a_0 b_0 . ( a_0 , b_0 ) -> a_0 = \ ( x_0 , y_0 ) -> x_0
|]

    it "does not type check" $ check program `shouldReturn` "2:5 error: 'y_0' is not used"


  describe "underscore may be unused" $ do

    let program = trim [r|
fst : forall a b. (a, b) -> a
fst (x, _) = x
|]

    it "parses" $ parse program `shouldReturn` trim [r|
fst_0 : forall a_0 b_0 . ( a_0 , b_0 ) -> a_0 = \ ( x_0 , _ ) -> x_0
|]

    it "type checks" $ check program `shouldReturn` trim [r|
fst_0 : forall a_0 b_0 . ( a_0 , b_0 ) -> a_0 = \ ( [a_0] x_0 , [b_0] _0 ) -> [a_0] x_0
|]


  describe "unused read variable" $ do

    let program = trim [r|
fst : forall a b. (a, b) -> a
fst (x, y) = read y in x
|]

    it "parses" $ parse program `shouldReturn` trim [r|
fst_0 : forall a_0 b_0 . ( a_0 , b_0 ) -> a_0 = \ ( x_0 , y_0 ) -> read y_0 in x_0
|]

    it "does not type checks" $ check program `shouldReturn` "2:14 error: 'y_0' is not used"


  describe "used read variable" $ do

    let program = trim [r|
fst : forall a b. (a, b) -> a
fst (x, y) = read y in x defer y
|]

    it "parses" $ parse program `shouldReturn` trim [r|
fst_0 : forall a_0 b_0 . ( a_0 , b_0 ) -> a_0 = \ ( x_0 , y_0 ) -> read y_0 in x_0 defer y_0
|]

    it "type checks" $ check program `shouldReturn` trim [r|
fst_0 : forall a_0 b_0 . ( a_0 , b_0 ) -> a_0 = \ ( [a_0] x_0 , [b_0] y_0 ) -> read y_0 in [a_0] [a_0] x_0 defer [& 'l0 b_0] y_0
|]



view = describe "polymorphic view pattern match" $ do

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
  return std::function([=](praxis::apply<v_0, praxis::Pair<a_0, b_0>> temp_0_){
    auto temp_1_ = temp_0_.first();
    auto temp_2_ = temp_0_.second();
    auto x_0 = std::move(temp_1_);
    auto y_0 = std::move(temp_2_);
    return praxis::mkPair(std::move(y_0), std::move(x_0));
    throw praxis::BindFail("3:6");
  });
};
|]

  it "compiles" $ compile program `shouldReturn` True



swap = describe "polymorphic function (swap)" $ do

  let program = [r|
swap : forall a b. (a, b) -> (b, a)
swap (a, b) = (b, a)
|]

  it "parses" $ parse program `shouldReturn` trim [r|
swap_0 : forall a_0 b_0 . ( a_0 , b_0 ) -> ( b_0 , a_0 ) = \ ( a_0 , b_0 ) -> ( b_0 , a_0 )
|]

  it "type checks" $ check program `shouldReturn` trim [r|
swap_0 : forall a_0 b_0 . ( a_0 , b_0 ) -> ( b_0 , a_0 ) = \ ( [a_0] a_0 , [b_0] b_0 ) -> ( [b_0] b_0 , [a_0] a_0 )
|]

  it "evaluates" $ do
    interpret program "swap (0, 1)"      `shouldReturn` "(1, 0)"
    interpret program "swap (True, 1)"   `shouldReturn` "(1, True)"
    interpret program "swap (1, 2, 3)"   `shouldReturn` "((2, 3), 1)"
    interpret program "swap ((2, 3), 1)" `shouldReturn` "(1, (2, 3))"
    interpret program "swap (\"abc\", 0)" `shouldReturn` "(0, \"abc\")"

  it "translates" $ translate program `shouldReturn` trim [r|
/* 2:1 */
auto swap_0 = []<typename a_0, typename b_0>(){
  return std::function([=](praxis::Pair<a_0, b_0> temp_0_){
    auto temp_1_ = temp_0_.first();
    auto temp_2_ = temp_0_.second();
    auto a_0 = std::move(temp_1_);
    auto b_0 = std::move(temp_2_);
    return praxis::mkPair(std::move(b_0), std::move(a_0));
    throw praxis::BindFail("3:6");
  });
};
|]



copy = describe "polymorphic function with constraint (copy)" $ do

  let program = [r|
copy : forall a | Copy a. a -> (a, a)
copy x = (x, x)
|]

  it "parses" $ parse program `shouldReturn` trim [r|
copy_0 : forall a_0 | Copy a_0 . a_0 -> ( a_0 , a_0 ) = \ x_0 -> ( x_0 , x_0 )
|]

  it "type checks" $ check program `shouldReturn` trim [r|
copy_0 : forall a_0 | Copy a_0 . a_0 -> ( a_0 , a_0 ) = \ [a_0] x_0 -> ( [a_0] x_0 , [a_0] x_0 )
|]

  it "evaluates" $ do
    interpret program "copy 0"         `shouldReturn` "(0, 0)"
    interpret program "copy (0, True)" `shouldReturn` "((0, True), (0, True))"



either = describe "polymorphic data type (Either)" $ do

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



fun = describe "polymorphic data type (Fun)" $ do

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

  it "evaluates" $ do
    interpret program "(unbox_fun id_fun ()) 4"  `shouldReturn` "4"



mutualRecursion = describe "mutual recursion" $ do

  let program = [r|
rec
  is_even = cases
    0 -> True
    n -> is_odd (n - 1)

  is_odd = cases
    0 -> False
    n -> is_even (n - 1)
|]

  it "parses" $ parse program `shouldReturn` trim [r|
rec
  is_even_0 = cases
    0 -> True
    n_0 -> is_odd_0 subtract_int ( n_0 , 1 )
  is_odd_0 = cases
    0 -> False
    n_1 -> is_even_0 subtract_int ( n_1 , 1 )
|]

  it "type checks" $ check program `shouldReturn` trim [r|
rec
  is_even_0 = [Int -> Bool] cases
    [Int] 0 -> [Bool] True
    [Int] n_0 -> [Int -> Bool] is_odd_0 [( Int , Int ) -> Int] subtract_int ( [Int] n_0 , [Int] 1 )
  is_odd_0 = [Int -> Bool] cases
    [Int] 0 -> [Bool] False
    [Int] n_1 -> [Int -> Bool] is_even_0 [( Int , Int ) -> Int] subtract_int ( [Int] n_1 , [Int] 1 )
|]

  it "translates" $ translate program `shouldReturn` trim [r|
auto temp_0_ = [](auto temp_1_) -> std::tuple<std::function<bool(int)>, std::function<bool(int)>> {
  return std::tuple{
    /* 2:1 */
    std::function([=](int temp_2_){
      auto [is_even_0, is_odd_0] = temp_1_(temp_1_);
      if (temp_2_ == 0) {
        return true;
      }
      auto n_0 = std::move(temp_2_);
      return std::move(is_odd_0)(std::move(subtract_int)(praxis::mkPair(std::move(n_0), 1)));
      throw praxis::CaseFail("3:13");
    }),
    /* 2:1 */
    std::function([=](int temp_3_){
      auto [is_even_0, is_odd_0] = temp_1_(temp_1_);
      if (temp_3_ == 0) {
        return false;
      }
      auto n_1 = std::move(temp_3_);
      return std::move(is_even_0)(std::move(subtract_int)(praxis::mkPair(std::move(n_1), 1)));
      throw praxis::CaseFail("7:12");
    })
  };
};
auto [is_even_0, is_odd_0] = temp_0_(temp_0_);
|]

  it "compiles" $ compile program `shouldReturn` True

  it "evaluates" $ do
    interpret program "is_even 0" `shouldReturn` "True"
    interpret program "is_even 1" `shouldReturn` "False"
    interpret program "is_even 2" `shouldReturn` "True"
    interpret program "is_even 3" `shouldReturn` "False"
    interpret program "is_odd 0" `shouldReturn` "False"
    interpret program "is_odd 1" `shouldReturn` "True"
    interpret program "is_odd 2" `shouldReturn` "False"
    interpret program "is_odd 3" `shouldReturn` "True"



list = describe "quantified type operators (List)" $ do

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
struct ListImpl : std::variant<praxis::Unit, praxis::Pair<a_0, List<a_0>>> {
  template<size_t index>
  inline const auto& get() const { return std::get<index>(*this); }
  template<size_t index>
  inline auto& get() { return std::get<index>(*this); }
};
static constexpr size_t Nil = 0;
static constexpr size_t Cons = 1;
auto mkNil = []<typename a_0>(){
  return std::function([](praxis::Unit&& arg){
    return praxis::mkBox<List>(std::in_place_index<Nil>, std::move(arg));
  });
};
auto mkCons = []<typename a_0>(){
  return std::function([](praxis::Pair<a_0, List<a_0>>&& arg){
    return praxis::mkBox<List>(std::in_place_index<Cons>, std::move(arg));
  });
};
auto temp_0_ = [](auto temp_1_){
  return std::tuple{
    /* 4:1 */
    [=]<praxis::View v_0, typename a_1, typename b_0>(){
      return std::function([=](std::function<b_0(praxis::apply<v_0, a_1>)> temp_2_){
        auto [map_0] = temp_1_(temp_1_);
        auto f_0 = std::move(temp_2_);
        return std::function([=](praxis::apply<v_0, List<a_1>> temp_3_){
          if (temp_3_.index() == Nil) {
            auto temp_4_ = temp_3_.template get<Nil>();
            return mkNil.template operator()<b_0>()(praxis::Unit{});
          }
          if (temp_3_.index() == Cons) {
            auto temp_5_ = temp_3_.template get<Cons>();
            auto temp_6_ = temp_5_.first();
            auto temp_7_ = temp_5_.second();
            auto x_0 = std::move(temp_6_);
            auto xs_0 = std::move(temp_7_);
            return mkCons.template operator()<b_0>()(praxis::mkPair(std::move(f_0)(std::move(x_0)), std::move(map_0).template operator()<v_0, a_1, b_0>()(std::move(f_0))(std::move(xs_0))));
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
    std::function([=](praxis::apply<praxis::View::REF, List<int>> temp_10_){
      auto [sum_0] = temp_9_(temp_9_);
      if (temp_10_.index() == Nil) {
        auto temp_11_ = temp_10_.template get<Nil>();
        return 0;
      }
      if (temp_10_.index() == Cons) {
        auto temp_12_ = temp_10_.template get<Cons>();
        auto temp_13_ = temp_12_.first();
        auto temp_14_ = temp_12_.second();
        auto x_1 = std::move(temp_13_);
        auto xs_1 = std::move(temp_14_);
        return std::move(add_int)(praxis::mkPair(std::move(x_1), std::move(sum_0)(std::move(xs_1))));
      }
      throw praxis::CaseFail("12:9");
    })
  };
};
auto [sum_0] = temp_8_(temp_8_);
|]



shadowing = describe "shadowing" $ do

-- TODO, the absence of rec means f (on the last line) is the top f. Very confusing... should be an error?
  let program = [r|
f x = f x where
  f : Int -> Int
  f x = x

g x = f x where rec
  f = cases
    0 -> 1
    n -> f (n - 1) * n
|]

  it "parses" $ parse program `shouldReturn` trim [r|
f_0 = \ x_0 -> f_1 x_0 where
  f_1 : Int -> Int = \ x_1 -> x_1
g_0 = \ x_2 -> f_2 x_2 where
  rec
    f_2 = cases
      0 -> 1
      n_0 -> multiply_int ( f_2 subtract_int ( n_0 , 1 ) , n_0 )
|]

  it "type checks" $ check program `shouldReturn` trim [r|
f_0 = \ [Int] x_0 -> [Int] [Int -> Int] f_1 [Int] x_0 where
  f_1 : Int -> Int = \ [Int] x_1 -> [Int] x_1
g_0 = \ [Int] x_2 -> [Int] [Int -> Int] f_2 [Int] x_2 where
  rec
    f_2 = [Int -> Int] cases
      [Int] 0 -> [Int] 1
      [Int] n_0 -> [( Int , Int ) -> Int] multiply_int ( [Int -> Int] f_2 [( Int , Int ) -> Int] subtract_int ( [Int] n_0 , [Int] 1 ) , [Int] n_0 )
|]

  it "evaluates" $ do
    interpret program "f 5" `shouldReturn` "5"
    interpret program "g 5" `shouldReturn` "120"



boxedReference = describe "boxed references" $ do

  let program = trim [r|
datatype Box [&v, a] = Box &v a

datatype List a = Nil () | Cons (a, List a)

box = Box "x"
|]

  it "parses" $ parse program `shouldReturn` trim [r|
datatype Box [ & v_0 , a_0 ] = Box & v_0 a_0
datatype List a_1 = Nil ( ) | Cons ( a_1 , List a_1 )
box_0 = Box "x"
|]

  it "type checks" $ check program `shouldReturn` trim [r|
datatype Box [ & v_0 , a_0 ] = [forall & v_0 a_0 . & v_0 a_0 -> Box [ & v_0 , a_0 ]] Box & v_0 a_0
datatype List a_1 = [forall a_1 . ( ) -> List a_1] Nil ( ) | [forall a_1 . ( a_1 , List a_1 ) -> List a_1] Cons ( a_1 , List a_1 )
box_0 = [& 'l0 String -> Box [ & 'l0 , String ]] Box [& 'l0 String] "x"
|]

  -- TODO should also try with ? instead of &
  it "evaluates" $ do

    interpret program "let xs = Cons (1, Cons (2, Cons (3, Nil ()))) in Box xs" `shouldReturn` trim [r|
error: found contradiction [1:50] & ^v3 List Int ?= List Int
|-> [1:50] List Int = List Int and & ^v3 List Int ?= List Int
|-> [1:50] & ^v3 List Int = List Int and Box [ & ^v3 , List Int ] = Box [ & ^v3 , List Int ]
|-> [1:50] & ^v3 List Int -> Box [ & ^v3 , List Int ] = List Int -> Box [ & ^v3 , List Int ]
|-> (function application)
|]

    interpret program [r|
do
  let xs = Cons (1, Cons (2, Cons (3, Nil ())))
  read xs in do
    Box xs
    () -- Note, Box xs can't escape the read
|] `shouldReturn` "()"



viewKinds = describe "view kinds" $ do

  describe "View & is a subkind of View ?" $ do

    let program = trim [r|
datatype Foo [?v, a] = Foo ?v a

datatype Bar [&v, a] = Bar (Foo [&v, a])
  |]

    it "kind checks" $ check program `shouldReturn` trim [r|
datatype Foo [ ? v_0 , a_0 ] = [forall ? v_0 a_0 . ? v_0 a_0 -> Foo [ ? v_0 , a_0 ]] Foo ? v_0 a_0
datatype Bar [ & v_1 , a_1 ] = [forall & v_1 a_1 . Foo [ & v_1 , a_1 ] -> Bar [ & v_1 , a_1 ]] Bar Foo [ & v_1 , a_1 ]
|]

  describe "View ? is not a subkind of View &" $ do

    let program = trim [r|
datatype Foo [&v, a] = Foo &v a

datatype Bar [?v, a] = Bar (Foo [?v, a])
  |]

    it "does not kind check" $ check program `shouldReturn` trim [r|
error: found contradiction [3:28] View ? ≤ View & and ^k3 ≤ Type
|-> [3:28] ( View ? , ^k3 ) ≤ ( View & , Type )
|-> (type function application)
|]



badDo = describe "do not ending in expression" $ do

  let program = trim [r|
foo = do
  let x = 1
  let y = 1
|]

  it "does not parse" $ check program `shouldReturn` "3:3 error: do block must end in an expression"


redeclVar = describe "variarble redeclaration" $ do

  let program = trim [r|
fst : forall a. (a, a) -> a
fst (a, a) = a
|]

  it "does not parse" $ parse program `shouldReturn` trim [r|
2:5 error: variables are not distinct
|]


redeclTyVar = describe "type variarble redeclaration" $ do

  let program = trim [r|
datatype Foo [a, a] = Foo a
|]

  it "does not parse" $ parse program `shouldReturn` "1:14 error: type variables are not distinct"


readUnsafe = describe "read safety" $ do

  let program = trim [r|
datatype List a = Nil () | Cons (a, List a)

x = Cons (1, Cons (2, Cons (3, Nil ())))

y = read x in (1, x)

|]

  it "parses" $ parse program `shouldReturn` trim [r|
datatype List a_0 = Nil ( ) | Cons ( a_0 , List a_0 )
x_0 = Cons ( 1 , Cons ( 2 , Cons ( 3 , Nil ( ) ) ) )
y_0 = read x_0 in ( 1 , x_0 )
|]

  it "does not type check" $ check program `shouldReturn` "error: found contradiction [5:5] 'l0 ref-free ( Int , & 'l0 ^t0 )\n|-> (safe read)"


spec :: Spec
spec = do

  describe "simple expressions" $ do

    let expressions =
          [ ("1 + 2", "1 + 2")
          , ("1 + 2 + 3", "(1 + 2) + 3")
          , ("1 + 2 * 3", "1 + (2 * 3)")
          , ("1 - 2 - 3", "(1 - 2) - 3")
          , ("1 - - 2", "1 - (- 2)")
          , ("f x 1 + g y * z", "(f (x 1)) + ((g y) * z)")
          , ("f x + f y + f z", "((f x) + (f y)) + (f z)")
          , ("(x, y, z)", "(x, (y, z))")
          , ("- 1 - - - 1", "(-1) - (- (-1))")
          ]

    forM_ expressions $ \(a, b) -> do
      it (show a ++ " parses like " ++ show b) $ do
        x <- parseAs IExp a
        y <- parseAs IExp b
        x `shouldBe` y
      it (show a ++ " parses idempotently") $ do
        x <- parseAs IExp a
        y <- parseAs IExp x
        x `shouldBe` y


  describe "simple types" $ do

    let types =
          [ ("Int -> Int -> Int", "Int -> (Int -> Int)")
          , ("A B C", "A (B C)")
          , ("Maybe Maybe a -> Maybe b", "(Maybe (Maybe a)) -> (Maybe b)")
          , ("forall a b. (a, b)", "forall a b . ( a, b )")
          , ("forall &r. &r Array Int -> ()", "forall &r . &r Array Int -> ()")
          , ("forall ?r. ?r Array Int -> ()", "forall ?r . ?r Array Int -> ()")
          ]

    forM_ types $ \(a, b) -> do
      it (show a ++ " parses like " ++ show b) $ do
        a <- parseAs IQType  a
        b <- parseAs IQType b
        a `shouldBe` b

    let types =
          [ "forall r &r. ()"
          , "forall r ?r. ()"
          , "forall r r. ()"
          , "forall &r &r. ()"
          , "forall ?r ?r. ()"
          , "forall &r ?r. ()"
          ]

    forM_ types $ \t -> do
      it (show t ++ " is not valid") $ do
        t' <- parseAs IQType t
        t' `shouldBe` "1:1 error: type variables are not distinct"


  describe "simple monomorphic programs" $ do
    doBlock
    tuple
    ifThenElse
    switch
    recursion
    mixfix

  describe "simple polymorphic programs" $ do
    view
    swap
    copy
    either
    fun
    readUnsafe
    unusedVar

  describe "complex programs" $ do
    mutualRecursion
    list
    shadowing
    boxedReference
    viewKinds

  describe "invalid programs" $ do
    badDo
    redeclVar
    redeclTyVar
