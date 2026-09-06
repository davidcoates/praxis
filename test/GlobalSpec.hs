{-# LANGUAGE QuasiQuotes #-}

module GlobalSpec where

import           Test.Hspec
import           Text.RawString.QQ

import           Introspect
import           Util


-- Globals are immortal and immutable: a use of a global is a read with a static lifetime.

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

xs = Cons (1, Cons (2, Nil ()))
|]

  describe "global read many times" $ do

    let program = list ++ [r|
total = sum xs + sum xs
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
xs = [( I32 , List I32 ) -> List I32] Cons ( [I32] 1 , [( I32 , List I32 ) -> List I32] Cons ( [I32] 2 , [( ) -> List I32] Nil [( )] ( ) ) )
total = [( I32 , I32 ) -> I32] add ( [&'static List I32 -> I32] sum [&'static List I32] xs , [&'static List I32 -> I32] sum [&'static List I32] xs )
|]

    it "evals" $ runEvaluate program "total" `shouldReturn` "6"


  describe "global consumed" $ do

    let program = list ++ [r|
gone = consume xs
|]

    it "does not type check" $ runPretty (check ProgramT program) `shouldReturn` trim [r|
type check error: unable to satisfy: @ ~ &'static
  | derived from: List I32 -> ( ) ~ &'static List I32 -> ( )
  | primary cause: application [List I32 -> ( )] consume ($) [&'static List I32] xs at 18:8
  | secondary cause: application [( I32 , List I32 ) -> List I32] Cons ($) ( [I32] 1 , [( ^t15 , List ^t15 ) -> List ^t15] Cons ( [!^s2] 2 , [( ) -> List ^t17] Nil [( )] ( ) ) ) at 16:6
|]


  describe "global aliased" $ do

    let program = list ++ [r|
ys = xs
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
xs = [( I32 , List I32 ) -> List I32] Cons ( [I32] 1 , [( I32 , List I32 ) -> List I32] Cons ( [I32] 2 , [( ) -> List I32] Nil [( )] ( ) ) )
ys = [&'static List I32] xs
|]

    it "evals" $ runEvaluate program "sum ys" `shouldReturn` "3"


  describe "global function used as a value many times" $ do

    let program = [r|
inc : I32 -> I32
inc x = x + 1

twice : (I32 -> I32, I32) -> I32
twice (f, x) = f (f x)

both = (twice (inc, 1), twice (inc, 2))
|]

    it "type checks" $ runPretty (check ProgramT program) `shouldReturn` trim [r|
inc : I32 -> I32 = \ [I32] x -> [( I32 , I32 ) -> I32] add ( [I32] x , [I32] 1 )
twice : ( I32 -> I32 , I32 ) -> I32 = \ ( [I32 -> I32] f , [I32] x ) -> [I32 -> I32] f ( [I32 -> I32] f [I32] x )
both = ( [( I32 -> I32 , I32 ) -> I32] twice ( [I32 -> I32] inc , [I32] 1 ) , [( I32 -> I32 , I32 ) -> I32] twice ( [I32 -> I32] inc , [I32] 2 ) )
|]

    it "evals" $ runEvaluate program "both" `shouldReturn` "(3, 4)"


  describe "explicit read of a global" $ do

    let program = list ++ [r|
total = read xs in sum xs
|]

    it "evals" $ runEvaluate program "total" `shouldReturn` "3"
