{-# LANGUAGE QuasiQuotes #-}

module LiftSpec where

import           Test.Hspec
import           Text.RawString.QQ

import           Introspect
import           Util


-- Lifting: after lowering, all functions are top-level, and closures are explicit partial applications.

spec :: Spec
spec = do

  describe "local function (no captures)" $ do

    let program = [r|
f x = double x where
  double : I32 -> I32
  double n = n + n
|]

    it "lowers" $ runPretty (lower ProgramT program) `shouldReturn` trim [r|
double : I32 -> I32 = \ n -> add ( copy n , n )
f = \ x -> double x
|]

    it "evals" $ runEvaluate program "f 5" `shouldReturn` "10"


  describe "local function (captures)" $ do

    let program = [r|
f x = addX 3 where
  addX : I32 -> I32
  addX y = x + y
|]

    it "lowers" $ runPretty (lower ProgramT program) `shouldReturn` trim [r|
addX : ( I32 , I32 ) -> I32 = \ ( x , y ) -> add ( x , y )
f = \ x -> addX ( x , 3 )
|]

    it "evals" $ runEvaluate program "f 10" `shouldReturn` "13"


  describe "local function used as a value" $ do

    let program = [r|
apply : (I32 -> I32, I32) -> I32
apply (h, v) = h v

f x = apply (g, 1) where
  g : I32 -> I32
  g y = x + y
|]

    it "lowers" $ runPretty (lower ProgramT program) `shouldReturn` trim [r|
apply : ( I32 -> I32 , I32 ) -> I32 = \ ( h , v ) -> h v
g : ( I32 , I32 ) -> I32 = \ ( x , y ) -> add ( x , y )
f = \ x -> apply ( closure [ x ] g , 1 )
|]

    it "evals" $ runEvaluate program "f 5" `shouldReturn` "6"


  describe "anonymous function (captures)" $ do

    let program = [r|
make_adder : I32 -> I32 -> I32
make_adder n = \x -> x + n
|]

    it "lowers" $ runPretty (lower ProgramT program) `shouldReturn` trim [r|
make_adder_lambda : ( I32 , I32 ) -> I32 = \ ( n , x ) -> add ( x , n )
make_adder : I32 -> I32 -> I32 = \ n -> closure [ n ] make_adder_lambda
|]

    it "evals" $ runEvaluate program "make_adder 1 2" `shouldReturn` "3"


  describe "anonymous function (multiple captures)" $ do

    let program = [r|
f : I32 -> I32 -> I32 -> I32
f a b = \c -> a + b + c
|]

    -- Note: the two lifted functions have distinct names, which happen to display the same.
    it "lowers" $ runPretty (lower ProgramT program) `shouldReturn` trim [r|
f_lambda : ( ( I32 , I32 ) , I32 ) -> I32 = \ ( ( a , b ) , c ) -> add ( add ( a , b ) , c )
f_lambda : ( I32 , I32 ) -> I32 -> I32 = \ ( a , b ) -> closure [ a , b ] f_lambda
f : I32 -> I32 -> I32 -> I32 = \ a -> closure [ a ] f_lambda
|]

    it "evals" $ runEvaluate program "f 1 2 3" `shouldReturn` "6"


  describe "anonymous function (no captures)" $ do

    let program = [r|
apply : (I32 -> I32, I32) -> I32
apply (h, v) = h v

f x = apply (\y -> y * 2, x)
|]

    it "lowers" $ runPretty (lower ProgramT program) `shouldReturn` trim [r|
apply : ( I32 -> I32 , I32 ) -> I32 = \ ( h , v ) -> h v
f_lambda : I32 -> I32 = \ y -> multiply ( y , 2 )
f = \ x -> apply ( f_lambda , x )
|]

    it "evals" $ runEvaluate program "f 4" `shouldReturn` "8"


  describe "immediately applied anonymous function" $ do

    let program = [r|
f x = (\y -> y + x) 1
|]

    it "lowers" $ runPretty (lower ProgramT program) `shouldReturn` trim [r|
f_lambda : ( I32 , I32 ) -> I32 = \ ( x , y ) -> add ( y , x )
f = \ x -> f_lambda ( x , 1 )
|]

    it "evals" $ runEvaluate program "f 5" `shouldReturn` "6"


  describe "cases (captures)" $ do

    let program = [r|
f : I32 -> I32 -> I32
f n = cases
  0 -> n
  m -> m + n
|]

    it "lowers" $ runPretty (lower ProgramT program) `shouldReturn` trim [r|
f_lambda : ( I32 , I32 ) -> I32 = \ ( n , arg ) -> case arg of
  0 -> n
  m -> add ( m , n )
f : I32 -> I32 -> I32 = \ n -> closure [ n ] f_lambda
|]

    it "evals" $ do
      runEvaluate program "f 3 0" `shouldReturn` "3"
      runEvaluate program "f 3 4" `shouldReturn` "7"


  describe "where value bindings become lets" $ do

    let program = [r|
f x = go base where
  base : I32
  base = x * 2
  go : I32 -> I32
  go n = n + base
|]

    it "lowers" $ runPretty (lower ProgramT program) `shouldReturn` trim [r|
go : ( I32 , I32 ) -> I32 = \ ( base , n ) -> add ( n , base )
f = \ x -> let base = multiply ( x , 2 ) in go ( copy base , base )
|]

    it "evals" $ runEvaluate program "f 5" `shouldReturn` "20"


  describe "local polymorphic function (captures)" $ do

    let program = [r|
f x = (pairWith True, pairWith 'c') where
  pairWith : forall a. a -> (I32, a)
  pairWith y = (x, y)
|]

    it "lowers" $ runPretty (lower ProgramT program) `shouldReturn` trim [r|
pairWith : ( I32 , Bool ) -> ( I32 , Bool ) = \ ( x , y ) -> ( x , y )
pairWith : ( I32 , Char ) -> ( I32 , Char ) = \ ( x , y ) -> ( x , y )
f = \ x -> ( pairWith ( copy x , True ) , pairWith ( x , 'c' ) )
|]

    it "evals" $ runEvaluate program "f 1" `shouldReturn` "((1, True), (1, 'c'))"
