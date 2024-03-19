{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE QuasiQuotes       #-}
{-# LANGUAGE TypeFamilies      #-}
{-# LANGUAGE TypeOperators     #-}

module PraxisSpec where

import qualified Check             (check)
import           Common
import           Inbuilts
import           Executors
import           Introspect
import qualified Parse             (parse)
import           Praxis
import           Prelude           hiding (either)
import           Print
import           Term
import           Text.RawString.QQ
import           Value             (Value (..))

import           Control.Monad     (forM_)
import           Test.Hspec


instance (Term a, x ~ Annotation a) => Show (Tag (Source, Maybe x) a) where
  show x = fold (runPrintable (pretty x) Types)

run :: Show a => Praxis a -> IO String
run p = do
  x <- runSilent initialState p
  case x of
    Left e  -> return e
    Right y -> return (show y)

check :: String -> IO String
check s = run (Parse.parse s >>= Check.check :: Praxis (Annotated Program))

-- Helper for interperting a program followed by an expression and printing the resulting value
interpret :: String -> String -> IO String
interpret program exp = run $ do
    interpretProgram program
    interpretExp exp

trim :: String -> String
trim = init . tail

doBlock = describe "do" $ do

  let program = [r|
foo = do
  let x = 1
  ()
  let y = 2
  x + y
|]

  it "type checks" $ check program `shouldReturn` trim [r|
foo = [Int] let [Int] x_0 = [Int] 1 in [Int] [( )] ( ) seq [Int] let [Int] y_0 = [Int] 2 in [( Int , Int ) -> Int] add_int ( [Int] x_0 , [Int] y_0 )
|]


tuple = describe "tuple" $ do

  let program = "x = (1, True, \"abc\")"

  it "type checks" $ check program `shouldReturn` trim [r|
x = ( [Int] 1 , [Bool] True , [& 'l0 Array Char] "abc" )
|]




ifThenElse = describe "if then else (min)" $ do

  let program = "min (x, y) = if x < y then x else y"

  it "type checks" $ do
    check program `shouldReturn` [r|min = \ ( [Int] x_0 , [Int] y_0 ) -> [Int] if [( Int , Int ) -> Bool] lt_int ( [Int] x_0 , [Int] y_0 ) then [Int] x_0 else [Int] y_0|]

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

  it "type checks" $ check program `shouldReturn` trim [r|
sign : Int -> Int = \ [Int] n_0 -> [Int] switch
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

  it "type checks" $ check program `shouldReturn` trim [r|
rec
  fac = [Int -> Int] cases
    [Int] 0 -> [Int] 1
    [Int] n_0 -> [( Int , Int ) -> Int] multiply_int ( [Int] n_0 , [Int -> Int] fac [( Int , Int ) -> Int] subtract_int ( [Int] n_0 , [Int] 1 ) )
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

  it "evaluates" $ do
    interpret program "False <-> True <?> 1 <:> 0" `shouldReturn` "0"



unusedVar = describe "unused variable" $ do

  let program = trim [r|
fst : forall a b. (a, b) -> a
fst (x, y) = x
|]

  it "does not type check" $ check program `shouldReturn` "2:5 error: variable 'y_0' is not used"



disposal = describe "non-copyable terms must be disposed" $ do

  let bad = trim [r|
fst : forall a b. (a, b) -> a
fst (x, _) = x
|]

  it "does not type check" $ check bad `shouldReturn` trim [r|
error: found contradiction [2:5] Copy b_0
|-> (variable '_0' is not disposed of)
|]

  let good = trim [r|
fst : forall a b | Copy b. (a, b) -> a
fst (x, _) = x
|]

  it "type checks" $ check good `shouldReturn` trim [r|
fst : forall a_0 b_0 | Copy b_0 . ( a_0 , b_0 ) -> a_0 = \ ( [a_0] x_0 , [b_0] _0 ) -> [a_0] x_0
|]



swap = describe "polymorphic function (swap)" $ do

  let program = [r|
swap : forall a b. (a, b) -> (b, a)
swap (a, b) = (b, a)
|]

  it "type checks" $ check program `shouldReturn` trim [r|
swap : forall a_0 b_0 . ( a_0 , b_0 ) -> ( b_0 , a_0 ) = \ ( [a_0] a_0 , [b_0] b_0 ) -> ( [b_0] b_0 , [a_0] a_0 )
|]

  it "evaluates" $ do
    interpret program "swap (0, 1)"      `shouldReturn` "(1, 0)"
    interpret program "swap (True, 1)"   `shouldReturn` "(1, True)"
    interpret program "swap (1, 2, 3)"   `shouldReturn` "((2, 3), 1)"
    interpret program "swap ((2, 3), 1)" `shouldReturn` "(1, (2, 3))"
    interpret program "swap (\"abc\", 0)" `shouldReturn` "(0, ['a', 'b', 'c'])"



copy = describe "polymorphic function with constraint (copy)" $ do

  let program = [r|
copy : forall a | Copy a. a -> (a, a)
copy x = (x, x)
|]

  it "type checks" $ check program `shouldReturn` trim [r|
copy : forall a_0 | Copy a_0 . a_0 -> ( a_0 , a_0 ) = \ [a_0] x_0 -> ( [a_0] x_0 , [a_0] x_0 )
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

  it "type checks" $ check program `shouldReturn` trim [r|
type Fun [ a_0 , b_0 ] = [forall a_0 b_0 . ( a_0 -> b_0 ) -> Fun [ a_0 , b_0 ]] Fun ( a_0 -> b_0 )
unbox_fun : forall a_1 b_1 . Fun [ a_1 , b_1 ] -> a_1 -> b_1 = \ [Fun [ a_1 , b_1 ]] Fun [a_1 -> b_1] f_0 -> \ [a_1] x_0 -> [a_1 -> b_1] f_0 [a_1] x_0
id_fun : forall a_2 . ( ) -> Fun [ a_2 , a_2 ] = \ [( )] ( ) -> [( a_2 -> a_2 ) -> Fun [ a_2 , a_2 ]] Fun ( \ [a_2] x_1 -> [a_2] x_1 )
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

  it "type checks" $ check program `shouldReturn` trim [r|
rec
  f = [Int -> Int] cases
    [Int] 0 -> [Int] 1
    [Int] n_0 -> [( Int , Int ) -> Int] subtract_int ( [Int] n_0 , [Int -> Int] m [Int -> Int] f [( Int , Int ) -> Int] subtract_int ( [Int] n_0 , [Int] 1 ) )
  m = [Int -> Int] cases
    [Int] 0 -> [Int] 0
    [Int] n_1 -> [( Int , Int ) -> Int] subtract_int ( [Int] n_1 , [Int -> Int] f [Int -> Int] m [( Int , Int ) -> Int] subtract_int ( [Int] n_1 , [Int] 1 ) )
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



list = describe "quantified type operators (list)" $ do

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

  it "type checks" $ check program `shouldReturn` trim [r|
type List a_0 = cases
  [forall a_0 . ( ) -> List a_0] Nil ( )
  [forall a_0 . ( a_0 , List a_0 ) -> List a_0] Cons ( a_0 , List a_0 )
rec
  map : forall ? v_0 a_1 b_0 . ( ? v_0 a_1 -> b_0 ) -> ? v_0 List a_1 -> List b_0 = \ [? v_0 a_1 -> b_0] f_0 -> [? v_0 List a_1 -> List b_0] cases
    [? v_0 List a_1] Nil [( )] ( ) -> [( ) -> List b_0] Nil [( )] ( )
    [? v_0 List a_1] Cons ( [? v_0 a_1] x_0 , [? v_0 List a_1] xs_0 ) -> [( b_0 , List b_0 ) -> List b_0] Cons ( [? v_0 a_1 -> b_0] f_0 [? v_0 a_1] x_0 , ( [( ? v_0 a_1 -> b_0 ) -> ? v_0 List a_1 -> List b_0] map [? v_0 a_1 -> b_0] f_0 ) [? v_0 List a_1] xs_0 )
rec
  sum : forall & r_0 . & r_0 List Int -> Int = [& r_0 List Int -> Int] cases
    [& r_0 List Int] Nil [( )] ( ) -> [Int] 0
    [& r_0 List Int] Cons ( [Int] x_1 , [& r_0 List Int] xs_1 ) -> [( Int , Int ) -> Int] add_int ( [Int] x_1 , [& r_0 List Int -> Int] sum [& r_0 List Int] xs_1 )
|]

  it "evaluates" $ do
    interpret program [r|
do
  let xs = Cons (1, Cons (2, Cons (3, Nil ())))
  sum &xs defer free xs
|] `shouldReturn` "6"
    interpret program [r|
do
  let xs = Cons (1, Cons (2, Cons (3, Nil ())))
  let ys = (map (\x -> x * 2)) &xs
  free xs
  sum &ys defer free ys
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

  it "type checks" $ check program `shouldReturn` trim [r|
f = \ [Int] x_0 -> [Int] [Int -> Int] f_0 [Int] x_0 where
  f_0 : Int -> Int = \ [Int] x_1 -> [Int] x_1
g = \ [Int] x_2 -> [Int] [Int -> Int] f_1 [Int] x_2 where
  rec
    f_1 = [Int -> Int] cases
      [Int] 0 -> [Int] 1
      [Int] n_0 -> [( Int , Int ) -> Int] multiply_int ( [Int -> Int] f_1 [( Int , Int ) -> Int] subtract_int ( [Int] n_0 , [Int] 1 ) , [Int] n_0 )
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

  it "type checks" $ check program `shouldReturn` trim [r|
type Box [ & v_0 , a_0 ] = [forall a_0 & v_0 . & v_0 a_0 -> Box [ & v_0 , a_0 ]] Box & v_0 a_0
type List a_1 = cases
  [forall a_1 . ( ) -> List a_1] Nil ( )
  [forall a_1 . ( a_1 , List a_1 ) -> List a_1] Cons ( a_1 , List a_1 )
box = [& 'l0 Array Char -> Box [ & 'l0 , Array Char ]] Box [& 'l0 Array Char] "x"
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
  read xs in free (Box xs) -- Note, Box xs can't escape the read
  free xs
|] `shouldReturn` "()"



badDo1 = describe "do not ending in expression" $ do

  let program = trim [r|
foo = do
  let x = 1
  let y = 1
|]

  it "does not parse" $ check program `shouldReturn` "3:3 error: do block must end in an expression"


badDo2 = describe "do drops non-unit" $ do

  let program = trim [r|
foo = do
  let x = 1
  x
  x
|]

  it "does not type check" $ check program `shouldReturn` trim [r|
error: found contradiction [3:3] Int ~ ( ) ∧ Int o~ ( )
|-> [3:3] Int ~ ( )
|-> (expression in do block returns a non-unit but is ignored)
|]


redeclVar = describe "variarble redeclaration" $ do

  let program = trim [r|
fst : forall a. (a, a) -> a
fst (a, a) = a
|]

  it "does not type check" $ check program `shouldReturn` "2:5 error: variables are not distinct"


redeclTyVar = describe "type variarble redeclaration" $ do

  let program = trim [r|
type Foo [a, a] = cases
    Foo a
|]

  it "does not type check" $ check program `shouldReturn` "1:10 error: type variables are not distinct"


readUnsafe = describe "read safety" $ do

  let program = trim [r|
type List a = cases
  Nil
  Cons (a, List a)

x = Cons (1, Cons (2, Cons (3, Nil)))

y = read x in (1, x)

|]

  it "does not type check" $ check program `shouldReturn` "error: found contradiction [7:5] 'l0 ref-free ( Int , & 'l0 ^t0 )\n|-> (safe read)"


spec :: Spec
spec = do

  describe "simple expressions" $ do

    let parse :: String -> IO String
        parse s = run (Parse.parse s :: Praxis (Annotated Exp))

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
        x <- parse a
        y <- parse b
        x `shouldBe` y
      it (show a ++ " parses idempotently") $ do
        x <- parse a
        y <- parse x
        x `shouldBe` y


  describe "simple types" $ do

    let parse :: String -> IO String
        parse s = run (Parse.parse s :: Praxis (Annotated QType))

    let types =
          [ ("Int -> Int -> Int", "Int -> (Int -> Int)")
          , ("A B C", "A (B C)")
          , ("Maybe Maybe a -> Maybe b", "(Maybe (Maybe a)) -> (Maybe b)")
          , ("forall a b. (a, b)", "forall a b . ( a, b )")
          , ("forall &r. &r Array Char -> ()", "forall &r . &r Array Char -> ()")
          , ("forall ?r. ?r Array Char -> ()", "forall ?r . ?r Array Char -> ()")
          ]

    forM_ types $ \(a, b) -> do
      it (show a ++ " parses like " ++ show b) $ do
        a <- parse a
        b <- parse b
        a `shouldBe` b

    let parse :: String -> IO String
        parse s = run (Parse.parse s :: Praxis (Annotated QType))

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
        t' <- parse t
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
    disposal

  describe "complex programs" $ do
    mutualRecursion
    list
    shadowing
    boxedReference

  describe "invalid programs" $ do
    badDo1
    badDo2
    redeclVar
    redeclTyVar
