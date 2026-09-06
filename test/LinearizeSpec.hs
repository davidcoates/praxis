{-# LANGUAGE QuasiQuotes #-}

module LinearizeSpec where

import           Test.Hspec
import           Text.RawString.QQ

import           Introspect
import           Util


-- Linearization: after lowering, every variable is consumed exactly once on every path, by inserting explicit copies and disposes.

spec :: Spec
spec = do

  let list = [r|
rec datatype List a = Nil () | Cons (a, List a)

rec
  sum : forall &r. &r List I32 -> I32
  sum = cases
    Nil ()       -> 0
    Cons (x, xs) -> x + sum xs

rec
  consume : List I32 -> ()
  consume = cases
    Nil ()       -> ()
    Cons (_, xs) -> consume xs
|]

  describe "read only variable" $ do

    let program = list ++ [r|
read_only : List I32 -> I32
read_only xs = read xs in sum xs
|]

    it "lowers" $ runPretty (lower ProgramT program) `shouldReturn` trim [r|
datatype boxed List = Nil ( ) | Cons ( I32 , List )
rec
  consume : List I32 -> ( ) = cases
    Nil ( ) -> ( )
    Cons ( hole , xs ) -> consume xs defer dispose hole
sum : &r List I32 -> I32 = cases
  Nil ( ) -> 0
  Cons ( x , xs ) -> add ( x , sum xs )
read_only : List I32 -> I32 = \ xs -> ( read xs in sum xs ) defer dispose xs
|]

    it "evals" $ runEvaluate program "read_only (Cons (1, Cons (2, Nil ())))" `shouldReturn` "3"


  describe "variable consumed in one branch" $ do

    let program = list ++ [r|
one_branch : (Bool, List I32) -> ()
one_branch (b, xs) = if b then consume xs else ()
|]

    it "lowers" $ runPretty (lower ProgramT program) `shouldReturn` trim [r|
datatype boxed List = Nil ( ) | Cons ( I32 , List )
rec
  consume : List I32 -> ( ) = cases
    Nil ( ) -> ( )
    Cons ( hole , xs ) -> consume xs defer dispose hole
one_branch : ( Bool , List I32 ) -> ( ) = \ ( b , xs ) -> if b then consume xs else ( ) defer dispose xs
|]

    it "evals" $ do
      runEvaluate program "one_branch (True, Cons (1, Nil ()))"  `shouldReturn` "()"
      runEvaluate program "one_branch (False, Cons (1, Nil ()))" `shouldReturn` "()"


  describe "variable consumed in a branch of an argument" $ do

    let program = list ++ [r|
nested : (Bool, List I32) -> ()
nested (b, xs) = consume (if b then xs else Nil ())
|]

    it "lowers" $ runPretty (lower ProgramT program) `shouldReturn` trim [r|
datatype boxed List = Nil ( ) | Cons ( I32 , List )
rec
  consume : List I32 -> ( ) = cases
    Nil ( ) -> ( )
    Cons ( hole , xs ) -> consume xs defer dispose hole
nested : ( Bool , List I32 ) -> ( ) = \ ( b , xs ) -> consume ( if b then xs else Nil ( ) defer dispose xs )
|]

    it "evals" $ runEvaluate program "nested (False, Cons (1, Nil ()))" `shouldReturn` "()"


  describe "variable consumed in a switch" $ do

    let program = list ++ [r|
in_switch : (I32, List I32) -> I32
in_switch (n, xs) = switch
  n < 0  -> 0
  n == 0 -> read xs in sum xs
  n > 0  -> consume xs seq n
|]

    it "lowers" $ runPretty (lower ProgramT program) `shouldReturn` trim [r|
datatype boxed List = Nil ( ) | Cons ( I32 , List )
rec
  consume : List I32 -> ( ) = cases
    Nil ( ) -> ( )
    Cons ( hole , xs ) -> consume xs defer dispose hole
sum : &r List I32 -> I32 = cases
  Nil ( ) -> 0
  Cons ( x , xs ) -> add ( x , sum xs )
in_switch : ( I32 , List I32 ) -> I32 = \ ( n , xs ) -> switch
  lt ( copy n , 0 ) -> ( 0 defer dispose n ) defer dispose xs
  eq ( copy n , 0 ) -> ( ( read xs in sum xs ) defer dispose n ) defer dispose xs
  gt ( copy n , 0 ) -> consume xs seq n
|]

    it "evals" $ do
      runEvaluate program "in_switch (-1, Cons (7, Nil ()))" `shouldReturn` "0"
      runEvaluate program "in_switch (0, Cons (7, Nil ()))"  `shouldReturn` "7"
      runEvaluate program "in_switch (1, Cons (7, Nil ()))"  `shouldReturn` "1"


  describe "variable bound by let" $ do

    let program = list ++ [r|
let_scope : List I32 -> I32
let_scope xs = let ys = xs in read ys in sum ys
|]

    it "lowers" $ runPretty (lower ProgramT program) `shouldReturn` trim [r|
datatype boxed List = Nil ( ) | Cons ( I32 , List )
rec
  consume : List I32 -> ( ) = cases
    Nil ( ) -> ( )
    Cons ( hole , xs ) -> consume xs defer dispose hole
sum : &r List I32 -> I32 = cases
  Nil ( ) -> 0
  Cons ( x , xs ) -> add ( x , sum xs )
let_scope : List I32 -> I32 = \ xs -> let ys = xs in ( read ys in sum ys ) defer dispose ys
|]

    it "evals" $ runEvaluate program "let_scope (Cons (4, Nil ()))" `shouldReturn` "4"


  describe "copyable variables used once are moved" $ do

    let program = [r|
copy_only : (I32, I32) -> I32
copy_only (x, y) = read y in x + y
|]

    it "lowers" $ runPretty (lower ProgramT program) `shouldReturn` trim [r|
copy_only : ( I32 , I32 ) -> I32 = \ ( x , y ) -> read y in add ( x , y )
|]


  describe "explicit dispose" $ do

    let program = list ++ [r|
explicit : List I32 -> ()
explicit xs = dispose xs
|]

    it "type checks" $ runPretty (check ProgramT program) `shouldReturn` trim [r|
rec
  datatype boxed List a = [forall a . ( ) -> List a] Nil ( ) | [forall a . ( a , List a ) -> List a] Cons ( a , List a )
rec
  sum : forall &r . &r List I32 -> I32 = [&r List I32 -> I32] cases
    [&r List I32] Nil [( )] ( ) -> [I32] 0
    [&r List I32] Cons ( [I32] x , [&r List I32] xs ) -> [( I32 , I32 ) -> I32] add ( [I32] x , [&r List I32 -> I32] sum [&r List I32] xs )
rec
  consume : List I32 -> ( ) = [List I32 -> ( )] cases
    [List I32] Nil [( )] ( ) -> [( )] ( )
    [List I32] Cons ( [I32] hole , [List I32] xs ) -> [List I32 -> ( )] consume [List I32] xs
explicit : List I32 -> ( ) = \ [List I32] xs -> [List I32 -> ( )] dispose [List I32] xs
|]

    it "evals" $ runEvaluate program "explicit (Cons (1, Nil ()))" `shouldReturn` "()"


  describe "not disposable (read only)" $ do

    let program = [r|
len : forall &r a. &r a -> I32
len _ = 0

f : forall a. a -> I32
f x = read x in len x
|]

    it "does not type check" $ runPretty (check ProgramT program) `shouldReturn` trim [r|
type check error: unable to satisfy: a : Dispose
  | primary cause: variable x is not consumed at 6:3
  | secondary causes:
  | - function f with signature forall a . a -> I32 at 5:1
  | - application [&^r0 ^t3 -> I32] len ($) [&'l0 a] x at 6:17
|]


  describe "not disposable (one branch)" $ do

    let program = [r|
g : forall a. (Bool, a, a -> ()) -> ()
g (b, x, k) = if b then k x else ()
|]

    it "does not type check" $ runPretty (check ProgramT program) `shouldReturn` trim [r|
type check error: unable to satisfy: a : Dispose
  | primary cause: variable x is not consumed in every branch at 3:15
  | secondary causes:
  | - function g with signature forall a . ( Bool , a , a -> ( ) ) -> ( ) at 2:1
  | - application [a -> ( )] k ($) [a] x at 3:25
|]


  describe "disposable (one branch)" $ do

    let program = [r|
g : forall a | a : Dispose. (Bool, a, a -> ()) -> ()
g (b, x, k) = if b then k x else ()
|]

    it "type checks" $ runPretty (check ProgramT program) `shouldReturn` trim [r|
g : forall a | a : Dispose . ( Bool , a , a -> ( ) ) -> ( ) = \ ( [Bool] b , [a] x , [a -> ( )] k ) -> [( )] if [Bool] b then [a -> ( )] k [a] x else [( )] ( )
|]


  describe "not disposable (consumed in a later switch condition)" $ do

    let program = [r|
g : forall a. (Bool, a, a -> Bool) -> ()
g (b, x, k) = switch
  b   -> ()
  k x -> ()
|]

    it "does not type check" $ runPretty (check ProgramT program) `shouldReturn` trim [r|
type check error: unable to satisfy: a : Dispose
  | primary cause: variable x is not consumed in every branch at 3:15
  | secondary causes:
  | - function g with signature forall a . ( Bool , a , a -> Bool ) -> ( ) at 2:1
  | - application [a -> Bool] k ($) [a] x at 5:3
|]


  describe "disposable (consumed in a later switch condition)" $ do

    let program = list ++ [r|
g : (Bool, List I32) -> ()
g (b, xs) = switch
  b                  -> ()
  read xs in sum xs > 0 -> ()
  True               -> consume xs
|]

    it "lowers" $ runPretty (lower ProgramT program) `shouldReturn` trim [r|
datatype boxed List = Nil ( ) | Cons ( I32 , List )
rec
  consume : List I32 -> ( ) = cases
    Nil ( ) -> ( )
    Cons ( hole , xs ) -> consume xs defer dispose hole
sum : &r List I32 -> I32 = cases
  Nil ( ) -> 0
  Cons ( x , xs ) -> add ( x , sum xs )
g : ( Bool , List I32 ) -> ( ) = \ ( b , xs ) -> switch
  b -> ( ) defer dispose xs
  read xs in gt ( sum xs , 0 ) -> ( ) defer dispose xs
  True -> consume xs
|]

    it "evals" $ do
      runEvaluate program "g (True, Cons (1, Nil ()))"  `shouldReturn` "()"
      runEvaluate program "g (False, Cons (1, Nil ()))" `shouldReturn` "()"


  describe "function used twice" $ do

    let program = [r|
use_twice : (I32 -> I32) -> I32
use_twice f = f (f 1)
|]

    it "lowers" $ runPretty (lower ProgramT program) `shouldReturn` trim [r|
use_twice : ( I32 -> I32 ) -> I32 = \ f -> copy f ( f 1 )
|]

    it "evals" $ runEvaluate program "use_twice (\\x -> x + 1)" `shouldReturn` "3"


  describe "variable captured then used" $ do

    let program = [r|
f x = (g, x) where
  g : I32 -> I32
  g y = x + y
|]

    it "lowers" $ runPretty (lower ProgramT program) `shouldReturn` trim [r|
g : ( I32 , I32 ) -> I32 = \ ( x , y ) -> add ( x , y )
f = \ x -> ( let x_copy = copy x in closure [ x_copy ] g , x )
|]

    it "evals" $ runEvaluate program "let (h, v) = f 1 in h v" `shouldReturn` "2"


  describe "unused copyable variable" $ do

    let program = [r|
const_zero : I32 -> I32
const_zero _ = 0
|]

    it "lowers" $ runPretty (lower ProgramT program) `shouldReturn` trim [r|
const_zero : I32 -> I32 = \ hole -> 0 defer dispose hole
|]


  describe "copy in a branch, then used after" $ do

    let program = [r|
f : (Bool, I32) -> I32
f (b, x) = (if b then x else 0) + x
|]

    it "lowers" $ runPretty (lower ProgramT program) `shouldReturn` trim [r|
f : ( Bool , I32 ) -> I32 = \ ( b , x ) -> add ( if b then copy x else 0 , x )
|]

    it "evals" $ do
      runEvaluate program "f (True, 3)"  `shouldReturn` "6"
      runEvaluate program "f (False, 3)" `shouldReturn` "3"


  describe "different number of uses in each branch" $ do

    let program = [r|
f : (Bool, I32) -> I32
f (b, x) = if b then x + x else x
|]

    it "lowers" $ runPretty (lower ProgramT program) `shouldReturn` trim [r|
f : ( Bool , I32 ) -> I32 = \ ( b , x ) -> if b then add ( copy x , x ) else x
|]

    it "evals" $ do
      runEvaluate program "f (True, 3)"  `shouldReturn` "6"
      runEvaluate program "f (False, 3)" `shouldReturn` "3"


  describe "copy within a read of a copyable variable" $ do

    let program = [r|
f : I32 -> I32
f x = read x in x + x
|]

    it "lowers" $ runPretty (lower ProgramT program) `shouldReturn` trim [r|
f : I32 -> I32 = \ x -> read x in add ( copy x , x )
|]

    it "evals" $ runEvaluate program "f 3" `shouldReturn` "6"


  describe "copy of a pair containing a function" $ do

    let program = [r|
apply_both : (I32 -> I32, I32) -> I32
apply_both p = fst p + snd p where
  fst : (I32 -> I32, I32) -> I32
  fst (f, n) = f n
  snd : (I32 -> I32, I32) -> I32
  snd (_, n) = n
|]

    it "lowers" $ runPretty (lower ProgramT program) `shouldReturn` trim [r|
fst : ( I32 -> I32 , I32 ) -> I32 = \ ( f , n ) -> f n
snd : ( I32 -> I32 , I32 ) -> I32 = \ ( hole , n ) -> n defer dispose hole
apply_both : ( I32 -> I32 , I32 ) -> I32 = \ p -> add ( fst ( copy p ) , snd p )
|]

    it "evals" $ runEvaluate program "apply_both (\\x -> x * 2, 5)" `shouldReturn` "15"
