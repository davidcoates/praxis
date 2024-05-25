{-# LANGUAGE QuasiQuotes #-}

module ExpSpec where

import           Test.Hspec
import           Text.RawString.QQ

import           Introspect
import           Util


spec :: Spec
spec = do

  describe "do" $ do

    let program = [r|
foo = do
  let x = 1
  ()
  let y = 2
  x + y
|]

    it "parses" $ runPretty (parse IProgram program) `shouldReturn` trim [r|
foo = let x = 1 in ( ) seq let y = 2 in add ( x , y )
|]

    it "type checks" $ runPretty (check IProgram program) `shouldReturn` trim [r|
foo_0 = [I32] let [I32] x_0 = [I32] 1 in [I32] [( )] ( ) seq [I32] let [I32] y_0 = [I32] 2 in [( I32 , I32 ) -> I32] add_0 ( [I32] x_0 , [I32] y_0 )
|]

    it "evals" $ runEvaluate program "foo" `shouldReturn` "3"


  describe "tuple" $ do

    let program = "x = (1, True, \"abc\")"
    it "parses" $ runPretty (parse IProgram program) `shouldReturn` trim [r|
x = ( 1 , True , "abc" )
|]

    it "type checks" $ runPretty (check IProgram program) `shouldReturn` trim [r|
x_0 = ( [I32] 1 , [Bool] True , [& 'l0 String] "abc" )
|]


  describe "if then else (min)" $ do

    let program = "min (x, y) = if x < y then x else y"

    it "parses" $ runPretty (parse IProgram program) `shouldReturn` trim [r|
min = \ ( x , y ) -> if lt ( x , y ) then x else y
|]

    it "type checks" $ runPretty (check IProgram program) `shouldReturn` trim [r|
min_0 = \ ( [I32] x_0 , [I32] y_0 ) -> [I32] if [( I32 , I32 ) -> Bool] lt_0 ( [I32] x_0 , [I32] y_0 ) then [I32] x_0 else [I32] y_0
|]

    it "evals" $ do
      runEvaluate program "min (1, 2)" `shouldReturn` "1"
      runEvaluate program "min (2, 1)" `shouldReturn` "1"
      runEvaluate program "min (1, 1)" `shouldReturn` "1"


  describe "switch (sign)" $ do

    let program = [r|
sign : I32 -> I32
sign n = switch
  n  < 0 -> -1
  n == 0 ->  0
  n  > 0 ->  1
|]

    it "parses" $ runPretty (parse IProgram program) `shouldReturn` trim [r|
sign : I32 -> I32 = \ n -> switch
  lt ( n , 0 ) -> -1
  eq ( n , 0 ) -> 0
  gt ( n , 0 ) -> 1
|]

    it "type checks" $ runPretty (check IProgram program) `shouldReturn` trim [r|
sign_0 : I32 -> I32 = \ [I32] n_0 -> [I32] switch
  [( I32 , I32 ) -> Bool] lt_0 ( [I32] n_0 , [I32] 0 ) -> [I32] -1
  [( I32 , I32 ) -> Bool] eq_0 ( [I32] n_0 , [I32] 0 ) -> [I32] 0
  [( I32 , I32 ) -> Bool] gt_0 ( [I32] n_0 , [I32] 0 ) -> [I32] 1
|]

    it "evals" $ do
      runEvaluate program "sign 0"    `shouldReturn` "0"
      runEvaluate program "sign 10"   `shouldReturn` "1"
      runEvaluate program "sign (-5)" `shouldReturn` "-1"
      runEvaluate program "sign -5"   `shouldReturn` "-1"
      runEvaluate program "sign - 5"  `shouldReturn` trim [r|
type check error: unable to satisfy: Integral ( I32 -> I32 )
  | primary cause: specialisation of 'subtract_0' at 1:6
  | secondary cause: application [( I32 -> I32 , I32 -> I32 ) -> I32 -> I32] subtract_0 ($) ( [I32 -> I32] sign_0 , [^t15] 5 ) at 1:1
|]  -- Note: Parses as "sign - 5" (binary subtract)
