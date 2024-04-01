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
int foo_0 = []()
{
  auto _temp_0 = 1;
  auto x_0 = _temp_0;
  return (Unit{}, [=]()
  {
    auto _temp_1 = 2;
    auto y_0 = _temp_1;
    return add_int(std::make_pair(x_0, y_0));
    throw MatchFail("5:7");
  }
  ());
  throw MatchFail("3:7");
}
();
|]

  it "compiles" $ compile program `shouldReturn` True



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
std::pair<int, std::pair<bool, std::string>> x_0 = std::make_pair(1, std::make_pair(true, "abc"));
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
error: found contradiction [1:1] Int ~ Int -> Int ∧ Int ~ Int
|-> [1:1] ( Int , Int ) ~ ( Int -> Int , Int ) ∧ Int ~ ^t6
|-> [1:1] ( Int , Int ) -> Int ~ ( Int -> Int , Int ) -> ^t6
|-> (function application)
|]  -- Note: Parses as "sign - 5" (binary subtract)


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

    it "does not type check" $ check program `shouldReturn` "2:5 error: variable 'y_0' is not used"


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

    it "does not type checks" $ check program `shouldReturn` "2:14 error: variable 'y_0' is not used"


  describe "used read variable" $ do

    let program = trim [r|
fst : forall a b. (a, b) -> a
fst (x, y) = read y in x defer y
|]

    it "parses" $ parse program `shouldReturn` trim [r|
fst_0 : forall a_0 b_0 . ( a_0 , b_0 ) -> a_0 = \ ( x_0 , y_0 ) -> read y_0 in x_0 defer y_0
|]

    it "type checks" $ check program `shouldReturn` trim [r|
fst_0 : forall a_0 b_0 . ( a_0 , b_0 ) -> a_0 = \ ( [a_0] x_0 , [b_0] y_0 ) -> [a_0] [a_0] x_0 defer [& 'l0 b_0] y_0
|]



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
type Either [a, b] = cases
    Left a
    Right b
|]

  it "parses" $ parse program `shouldReturn` trim [r|
type Either [ a_0 , b_0 ] = cases
  Left a_0
  Right b_0
|]

  it "type checks" $ check program `shouldReturn` trim [r|
type Either [ a_0 , b_0 ] = cases
  [forall a_0 b_0 . a_0 -> Either [ a_0 , b_0 ]] Left a_0
  [forall a_0 b_0 . b_0 -> Either [ a_0 , b_0 ]] Right b_0
|]

  it "evaluates" $ do
    interpret program "Left 0 : Either [Int, ()]"  `shouldReturn` "Left 0"
    interpret program "Right 1 : Either [(), Int]" `shouldReturn` "Right 1"



fun = describe "polymorphic data type (Fun)" $ do

  let program = [r|
type Fun [a, b] = Fun (a -> b)

unbox_fun : forall a b. Fun [a, b] -> a -> b
unbox_fun (Fun f) x = f x

-- FIXME unit shouldn't be required here since Fun [a, a] is shareable
id_fun : forall a. () -> Fun [a, a]
id_fun () = Fun (\x -> x)
|]

  it "parses" $ parse program `shouldReturn` trim [r|
type Fun [ a_0 , b_0 ] = Fun ( a_0 -> b_0 )
unbox_fun_0 : forall a_1 b_1 . Fun [ a_1 , b_1 ] -> a_1 -> b_1 = \ Fun f_0 -> \ x_0 -> f_0 x_0
id_fun_0 : forall a_2 . ( ) -> Fun [ a_2 , a_2 ] = \ ( ) -> Fun ( \ x_1 -> x_1 )
|]

  it "type checks" $ check program `shouldReturn` trim [r|
type Fun [ a_0 , b_0 ] = [forall a_0 b_0 . ( a_0 -> b_0 ) -> Fun [ a_0 , b_0 ]] Fun ( a_0 -> b_0 )
unbox_fun_0 : forall a_1 b_1 . Fun [ a_1 , b_1 ] -> a_1 -> b_1 = \ [Fun [ a_1 , b_1 ]] Fun [a_1 -> b_1] f_0 -> \ [a_1] x_0 -> [a_1 -> b_1] f_0 [a_1] x_0
id_fun_0 : forall a_2 . ( ) -> Fun [ a_2 , a_2 ] = \ [( )] ( ) -> [( a_2 -> a_2 ) -> Fun [ a_2 , a_2 ]] Fun ( \ [a_2] x_1 -> [a_2] x_1 )
|]

  it "evaluates" $ do
    interpret program "(unbox_fun id_fun ()) 4"  `shouldReturn` "4"



mutualRecursion = describe "mutual recursion" $ do

  let program = [r|
rec
  f = cases
    0 -> 1
    n -> n - m f (n - 1)

  m = cases
    0 -> 0
    n -> n - f m (n - 1)
|]

  it "parses" $ parse program `shouldReturn` trim [r|
rec
  f_0 = cases
    0 -> 1
    n_0 -> subtract_int ( n_0 , m_0 f_0 subtract_int ( n_0 , 1 ) )
  m_0 = cases
    0 -> 0
    n_1 -> subtract_int ( n_1 , f_0 m_0 subtract_int ( n_1 , 1 ) )
|]

  it "type checks" $ check program `shouldReturn` trim [r|
rec
  f_0 = [Int -> Int] cases
    [Int] 0 -> [Int] 1
    [Int] n_0 -> [( Int , Int ) -> Int] subtract_int ( [Int] n_0 , [Int -> Int] m_0 [Int -> Int] f_0 [( Int , Int ) -> Int] subtract_int ( [Int] n_0 , [Int] 1 ) )
  m_0 = [Int -> Int] cases
    [Int] 0 -> [Int] 0
    [Int] n_1 -> [( Int , Int ) -> Int] subtract_int ( [Int] n_1 , [Int -> Int] f_0 [Int -> Int] m_0 [( Int , Int ) -> Int] subtract_int ( [Int] n_1 , [Int] 1 ) )
|]

  it "evaluates" $ do
    interpret program "f 0" `shouldReturn` "1"
    interpret program "f 1" `shouldReturn` "1"
    interpret program "f 2" `shouldReturn` "2"
    interpret program "f 3" `shouldReturn` "2"
    interpret program "f 4" `shouldReturn` "3"
    interpret program "f 5" `shouldReturn` "3"
    interpret program "f 6" `shouldReturn` "4"
    interpret program "m 0" `shouldReturn` "0"
    interpret program "m 1" `shouldReturn` "0"
    interpret program "m 2" `shouldReturn` "1"
    interpret program "m 3" `shouldReturn` "2"
    interpret program "m 4" `shouldReturn` "2"
    interpret program "m 5" `shouldReturn` "3"
    interpret program "m 6" `shouldReturn` "4"



list = describe "quantified type operators (List)" $ do

  let program = [r|
type List a = cases
  Nil ()
  Cons (a, List a)

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
type List a_0 = cases
  Nil ( )
  Cons ( a_0 , List a_0 )
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
type List a_0 = cases
  [forall a_0 . ( ) -> List a_0] Nil ( )
  [forall a_0 . ( a_0 , List a_0 ) -> List a_0] Cons ( a_0 , List a_0 )
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
type Box [&v, a] = Box &v a

type List a = cases
  Nil ()
  Cons (a, List a)

box = Box "x"
|]

  it "parses" $ parse program `shouldReturn` trim [r|
type Box [ & v_0 , a_0 ] = Box & v_0 a_0
type List a_1 = cases
  Nil ( )
  Cons ( a_1 , List a_1 )
box_0 = Box "x"
|]

  it "type checks" $ check program `shouldReturn` trim [r|
type Box [ & v_0 , a_0 ] = [forall a_0 & v_0 . & v_0 a_0 -> Box [ & v_0 , a_0 ]] Box & v_0 a_0
type List a_1 = cases
  [forall a_1 . ( ) -> List a_1] Nil ( )
  [forall a_1 . ( a_1 , List a_1 ) -> List a_1] Cons ( a_1 , List a_1 )
box_0 = [& 'l0 String -> Box [ & 'l0 , String ]] Box [& 'l0 String] "x"
|]

  -- TODO should also try with ? instead of &
  it "evaluates" $ do

    interpret program "let xs = Cons (1, Cons (2, Cons (3, Nil ()))) in Box xs" `shouldReturn` trim [r|
error: found contradiction [1:50] & ^v3 List Int o~ List Int
|-> [1:50] List Int ~ List Int ∧ & ^v3 List Int o~ List Int
|-> [1:50] & ^v3 List Int ~ List Int ∧ Box [ & ^v3 , List Int ] ~ Box [ & ^v3 , List Int ]
|-> [1:50] & ^v3 List Int -> Box [ & ^v3 , List Int ] ~ List Int -> Box [ & ^v3 , List Int ]
|-> (function application)
|]

    interpret program [r|
do
  let xs = Cons (1, Cons (2, Cons (3, Nil ())))
  read xs in do
    Box xs
    () -- Note, Box xs can't escape the read
|] `shouldReturn` "()"



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
type Foo [a, a] = cases
    Foo a
|]

  it "does not parse" $ parse program `shouldReturn` "1:10 error: type variables are not distinct"


readUnsafe = describe "read safety" $ do

  let program = trim [r|
type List a = cases
  Nil
  Cons (a, List a)

x = Cons (1, Cons (2, Cons (3, Nil)))

y = read x in (1, x)

|]

  it "parses" $ parse program `shouldReturn` trim [r|
type List a_0 = cases
  Nil
  Cons ( a_0 , List a_0 )
x_0 = Cons ( 1 , Cons ( 2 , Cons ( 3 , Nil ) ) )
y_0 = read x_0 in ( 1 , x_0 )
|]

  it "does not type check" $ check program `shouldReturn` "error: found contradiction [7:5] 'l0 ref-free ( Int , & 'l0 ^t0 )\n|-> (safe read)"


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

  describe "invalid programs" $ do
    badDo
    redeclVar
    redeclTyVar
