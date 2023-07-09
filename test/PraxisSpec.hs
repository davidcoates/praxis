{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies      #-}
{-# LANGUAGE TypeOperators     #-}
{-# LANGUAGE QuasiQuotes     #-}

module PraxisSpec where

import qualified Check         (check)
import           Common
import           Inbuilts
import qualified Interpret     (interpret)
import           Introspect
import qualified Parse         (parse)
import           Praxis
import           Print
import           Term
import           Value         (Value (..))
import           Text.RawString.QQ

import           Control.Monad (forM_)
import           Test.Hspec


instance (Term a, x ~ Annotation a) => Show (Tag (Source, Maybe x) a) where
  show x = fold (runPrintable (pretty x) Types)

run :: Show a => Praxis a -> IO String
run p = do
  x <- runSilent initialState p
  case x of
    Just y  -> return (show y)
    Nothing -> error "failure" -- TODO could retreive the throw message somehow :thinking:

check :: String -> IO String
check s = run (Parse.parse s >>= Check.check :: Praxis (Annotated Program))

interpret :: String -> String -> IO String
interpret program exp = run $ do
    Interpret.interpret program :: Praxis (Annotated Program, ())
    (_, v) <- Interpret.interpret exp :: Praxis (Annotated Exp, Value)
    return v

trim :: String -> String
trim = init . tail

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
        parse s = run (Parse.parse s :: Praxis (Annotated Type))

    let types =
          [ ("Int -> Int -> Int", "Int -> (Int -> Int)")
          , ("A B C", "A (B C)")
          , ("Maybe Maybe a -> Maybe b", "(Maybe (Maybe a)) -> (Maybe b)")
          ]

    forM_ types $ \(a, b) -> do
      it (show a ++ " parses like " ++ show b) $ do
        x <- parse a
        y <- parse b
        x `shouldBe` y
      it (show a ++ " parses idempotently") $ do
        x <- parse a
        y <- parse x
        x `shouldBe` y


  describe "simple monomorphic programs" $ do

    describe "if then else (min)" $ do

      let program = "min (x, y) = if x < y then x else y"

      it "type checks" $ do
        check program `shouldReturn` [r|min = [( Int , Int ) -> Int] \ [( Int , Int )] ( [Int] x , [Int] y ) -> [Int] if [Bool] [( Int , Int ) -> Bool] lt_int [( Int , Int )] ( [Int] x , [Int] y ) then [Int] x else [Int] y|]

      it "evaluates" $ do
        interpret program "min (1, 2)" `shouldReturn` "1"
        interpret program "min (2, 1)" `shouldReturn` "1"
        interpret program "min (1, 1)" `shouldReturn` "1"


    describe "switch (sign)" $ do

      let program = [r|
sign : Int -> Int
sign n = switch
  n  < 0 -> -1
  n == 0 ->  0
  n  > 0 -> +1
|]

      it "type checks" $ do
        check program `shouldReturn` trim [r|
sign : Int -> Int = [Int -> Int] \ [Int] n -> [Int] switch
  [Bool] [( Int , Int ) -> Bool] lt_int [( Int , Int )] ( [Int] n , [Int] 0 ) -> [Int] [Int -> Int] negate_int [Int] 1
  [Bool] [( Int , Int ) -> Bool] eq_int [( Int , Int )] ( [Int] n , [Int] 0 ) -> [Int] 0
  [Bool] [( Int , Int ) -> Bool] gt_int [( Int , Int )] ( [Int] n , [Int] 0 ) -> [Int] [Int -> Int] unary_plus_int [Int] 1
|]

      it "evaluates" $ do
        interpret program "sign 0"    `shouldReturn` "0"
        interpret program "sign 10"   `shouldReturn` "1"
        interpret program "sign (-5)" `shouldReturn` "-1"
        interpret program "sign -5"   `shouldThrow` anyException -- Note: Parses as "sign - 5" (binary subtract)

    describe "recursion (factorial)" $ do

      let program = [r|
fac = cases
  0 -> 1
  n -> n * fac (n - 1)
|]

      it "type checks" $ do
        check program `shouldReturn` trim [r|
fac = [Int -> Int] cases
  [Int] 0 -> [Int] 1
  [Int] n -> [Int] [( Int , Int ) -> Int] multiply_int [( Int , Int )] ( [Int] n , [Int] [Int -> Int] fac [( Int , Int ) -> Int] subtract_int [( Int , Int )] ( [Int] n , [Int] 1 ) )
|]

      it "evaluates" $ do
        interpret program "fac 0"  `shouldReturn` "1"
        interpret program "fac 5"  `shouldReturn` "120"
        interpret program "fac 15" `shouldReturn` "1307674368000"

  describe "simple polymorphic programs" $ do

    describe "polymorphic function (swap)" $ do

      let program = [r|
swap : forall a b. (a, b) -> (b, a)
swap (a, b) = (b, a)
|]

      it "type checks" $ do
        check program `shouldReturn` trim [r|
swap : forall 't0 't1 . ( 't0 , 't1 ) -> ( 't1 , 't0 ) = [( 't0 , 't1 ) -> ( 't1 , 't0 )] \ [( 't0 , 't1 )] ( ['t0] a , ['t1] b ) -> [( 't1 , 't0 )] ( ['t1] b , ['t0] a )
|]

      it "evaluates" $ do
        interpret program "swap (0, 1)"      `shouldReturn` "(1, 0)"
        interpret program "swap (True, 1)"   `shouldReturn` "(1, True)"
        interpret program "swap (1, 2, 3)"   `shouldReturn` "((2, 3), 1)"
        interpret program "swap ((2, 3), 1)" `shouldReturn` "(1, (2, 3))"
        -- interpret program "swap (\"abc\", 0)" `shouldReturn` "(0, \"abc\")"


    describe "polymorphic function with constraint (copy)" $ do

      let program = [r|
copy : forall a. [Share a] => a -> (a, a)
copy x = (x, x)
|]

      it "type checks" $ do
        check program `shouldReturn` trim [r|
copy : forall 't0 . [ Share 't0 ] => 't0 -> ( 't0 , 't0 ) = ['t0 -> ( 't0 , 't0 )] \ ['t0] x -> [( 't0 , 't0 )] ( ['t0] x , ['t0] x )
|]

      it "evaluates" $ do
        interpret program "copy 0"         `shouldReturn` "(0, 0)"
        interpret program "copy (0, True)" `shouldReturn` "((0, True), (0, True))"


    describe "polymorphic data type (Either)" $ do

      let program = [r|
type Either [a, b] = cases
    Left a
    Right b
|]

      it "type checks" $ do
        check program `shouldReturn` trim [r|
type Either [ a , b ] = cases
  [forall a b . a -> Either [ a , b ]] Left a
  [forall a b . b -> Either [ a , b ]] Right b
|]

      it "evaluates" $ do
        interpret program "Left 0"  `shouldReturn` "Left 0"
        interpret program "Right 1" `shouldReturn` "Right 1"


    describe "polymorphic data type (Fun)" $ do

      let program = [r|
type Fun [a, b] = Fun (a -> b)

unbox_fun : forall a b. Fun [a, b] -> a -> b
unbox_fun (Fun f) x = f x

id_fun : forall a. Fun [a, a]
id_fun = Fun (\x -> x)
|]

      it "type checks" $ do
        check program `shouldReturn` trim [r|
type Fun [ a , b ] = [forall a b . ( a -> b ) -> Fun [ a , b ]] Fun ( a -> b )
unbox_fun : forall 't0 't1 . Fun [ 't0 , 't1 ] -> 't0 -> 't1 = [Fun [ 't0 , 't1 ] -> 't0 -> 't1] \ [Fun [ 't0 , 't1 ]] Fun ['t0 -> 't1] f -> ['t0 -> 't1] \ ['t0] x -> ['t1] ['t0 -> 't1] f ['t0] x
id_fun : forall 't2 . Fun [ 't2 , 't2 ] = [Fun [ 't2 , 't2 ]] [( 't2 -> 't2 ) -> Fun [ 't2 , 't2 ]] Fun ['t2 -> 't2] ( \ ['t2] x -> ['t2] x )
|]

      it "evaluates" $ do
        interpret program "(unbox_fun id_fun) 4"  `shouldReturn` "4"


  describe "complex programs" $ do

    describe "mutual recursion" $ do

      let program = [r|
f = cases
  0 -> 1
  n -> n - m f (n - 1)

m = cases
  0 -> 0
  n -> n - f m (n - 1)
|]

      it "type checks" $ do
        check program `shouldReturn` trim [r|
f = [Int -> Int] cases
  [Int] 0 -> [Int] 1
  [Int] n -> [Int] [( Int , Int ) -> Int] subtract_int [( Int , Int )] ( [Int] n , [Int] [Int -> Int] m [Int -> Int] f [( Int , Int ) -> Int] subtract_int [( Int , Int )] ( [Int] n , [Int] 1 ) )
m = [Int -> Int] cases
  [Int] 0 -> [Int] 0
  [Int] n -> [Int] [( Int , Int ) -> Int] subtract_int [( Int , Int )] ( [Int] n , [Int] [Int -> Int] f [Int -> Int] m [( Int , Int ) -> Int] subtract_int [( Int , Int )] ( [Int] n , [Int] 1 ) )
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


    describe "quantified type operators (list)" $ do

      let program = [r|
type List a = cases
  Nil
  Cons (a, List a)

map : forall ?v a b. (?v a -> b) -> ?v List a -> List b
map f = cases
  Nil          -> Nil
  Cons (x, xs) -> Cons (f x, (map f) xs)

sum : &List Int -> Int
sum = cases
  Nil          -> 0
  Cons (x, xs) -> x + sum xs
|]

      it "type checks" $ do
        check program `shouldReturn` trim [r|
type List a = cases
  [forall a . List a] Nil
  [forall a . ( a , List a ) -> List a] Cons ( a , List a )
map : forall ?'o0 't0 't1 . ( ?'o0 't0 -> 't1 ) -> ?'o0 List 't0 -> List 't1 = [( ?'o0 't0 -> 't1 ) -> ?'o0 List 't0 -> List 't1] \ [?'o0 't0 -> 't1] f -> [?'o0 List 't0 -> List 't1] cases
  [?'o0 List 't0] Nil -> [List 't1] Nil
  [?'o0 List 't0] Cons [?'o0 ( 't0 , List 't0 )] ( [?'o0 't0] x , [?'o0 List 't0] xs ) -> [List 't1] [( 't1 , List 't1 ) -> List 't1] Cons [( 't1 , List 't1 )] ( ['t1] [?'o0 't0 -> 't1] f [?'o0 't0] x , [List 't1] [?'o0 List 't0 -> List 't1] ( [( ?'o0 't0 -> 't1 ) -> ?'o0 List 't0 -> List 't1] map [?'o0 't0 -> 't1] f ) [?'o0 List 't0] xs )
sum : & List Int -> Int = [& List Int -> Int] cases
  [& List Int] Nil -> [Int] 0
  [& List Int] Cons [& ( Int , List Int )] ( [Int] x , [& List Int] xs ) -> [Int] [( Int , Int ) -> Int] add_int [( Int , Int )] ( [Int] x , [Int] [& List Int -> Int] sum [& List Int] xs )
|]

      it "evaluates" $ do
        interpret program [r|let xs = Cons (1, Cons (2, Cons (3, Nil))) in sum &xs|] `shouldReturn` "6"
        interpret program [r|let xs = Cons (1, Cons (2, Cons (3, Nil))) in let ys = (map (\x -> x * 2)) &xs in sum &ys|] `shouldReturn` "12"


    describe "shadowing" $ do

      let program = [r|
f x = f x where
  f : Int -> Int
  f x = x

g x = f x where
  f = cases
    0 -> 1
    n -> f (n - 1) * n
|]

      it "type checks" $ do
        check program `shouldReturn` trim [r|
f = [Int -> Int] \ [Int] x -> [Int] [Int] [Int -> Int] f [Int] x where
  f : Int -> Int = [Int -> Int] \ [Int] x -> [Int] x
g = [Int -> Int] \ [Int] x -> [Int] [Int] [Int -> Int] f [Int] x where
  f = [Int -> Int] cases
    [Int] 0 -> [Int] 1
    [Int] n -> [Int] [( Int , Int ) -> Int] multiply_int [( Int , Int )] ( [Int] [Int -> Int] f [( Int , Int ) -> Int] subtract_int [( Int , Int )] ( [Int] n , [Int] 1 ) , [Int] n )
|]

      it "evaluates" $ do
        interpret program "f 5" `shouldReturn` "5"
        interpret program "g 5" `shouldReturn` "120"
