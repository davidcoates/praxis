{-# LANGUAGE QuasiQuotes #-}

module LocalFnSpec where

import           Test.Hspec
import           Text.RawString.QQ

import           Introspect
import           Util


spec :: Spec
spec = do

  -- ----------------------------------------------------------------
  -- Monomorphic local functions
  -- ----------------------------------------------------------------

  describe "local mono function (no capture)" $ do

    let program = [r|
f x = double x where
  double : I32 -> I32
  double n = n + n
|]

    it "type checks" $ runPretty (check ProgramT program) `shouldReturn` trim [r|
f = \ [I32] x -> [I32] [I32 -> I32] double [I32] x where
  double : I32 -> I32 = \ [I32] n -> [( I32 , I32 ) -> I32] add ( [I32] n , [I32] n )
|]

    it "evals" $ runEvaluate program "f 5" `shouldReturn` "10"


  describe "local mono function (captures outer arg)" $ do

    let program = [r|
f x = addX 3 where
  addX : I32 -> I32
  addX y = x + y
|]

    it "evals" $ runEvaluate program "f 10" `shouldReturn` "13"


  describe "local mono function (captures two outer args)" $ do

    let program = [r|
f x y = addBoth 1 where
  addBoth : I32 -> I32
  addBoth z = x + y + z
|]

    it "evals" $ runEvaluate program "f 3 4" `shouldReturn` "8"


  describe "local mono function (captures three outer args)" $ do

    let program = [r|
f a b c = addAll 0 where
  addAll : I32 -> I32
  addAll n = a + b + c + n
|]

    it "evals" $ runEvaluate program "f 1 2 3" `shouldReturn` "6"


  describe "multiple local mono functions" $ do

    let program = [r|
compute x = step2 (step1 x) where
  step1 : I32 -> I32
  step1 n = n * 2
  step2 : I32 -> I32
  step2 n = n + 1
|]

    it "evals" $ runEvaluate program "compute 4" `shouldReturn` "9"


  describe "local mono functions calling each other" $ do

    let program = [r|
f x = outer x where
  inner : I32 -> I32
  inner n = n + 1
  outer : I32 -> I32
  outer n = inner (inner n)
|]

    it "evals" $ runEvaluate program "f 0" `shouldReturn` "2"


  describe "local mono function (result used multiple times)" $ do
    let program = [r|
f x = (inc x, inc x) where
  inc : I32 -> I32
  inc n = n + 1
|]

    it "evals" $ runEvaluate program "f 4" `shouldReturn` "(5, 5)"


  -- ----------------------------------------------------------------
  -- Polymorphic local functions
  -- ----------------------------------------------------------------

  describe "local poly function (no capture)" $ do

    let program = [r|
useSwap = (swap (1, True), swap (False, 2)) where
  swap : forall a b. (a, b) -> (b, a)
  swap (a, b) = (b, a)
|]

    it "evals" $ runEvaluate program "useSwap"
      `shouldReturn` "((True, 1), (2, False))"


  describe "local poly function (used at multiple types)" $ do

    let program = [r|
test = (pairWith 1 True, pairWith 'x' 2) where
  pairWith : forall a b. a -> b -> (a, b)
  pairWith a b = (a, b)
|]

    it "evals" $ runEvaluate program "test"
      `shouldReturn` "((1, True), ('x', 2))"


  describe "local poly function (two type params, used together)" $ do

    let program = [r|
test = (combine 1 True, combine 'x' 2) where
  combine : forall a b. a -> b -> (a, b)
  combine x y = (x, y)
|]

    it "evals" $ runEvaluate program "test"
      `shouldReturn` "((1, True), ('x', 2))"


  -- ----------------------------------------------------------------
  -- Nested where clauses
  -- ----------------------------------------------------------------

  describe "nested where clauses" $ do

    let program = [r|
f x = outer x where
  outer : I32 -> I32
  outer n = inner n where
    inner : I32 -> I32
    inner m = m * m
|]

    it "evals" $ runEvaluate program "f 4" `shouldReturn` "16"


  describe "local value binding in where" $ do

    let program = [r|
f x = result where
  result : I32
  result = x * x + x
|]

    it "evals" $ do
      runEvaluate program "f 3" `shouldReturn` "12"
      runEvaluate program "f 0" `shouldReturn` "0"


  describe "mixed value and function bindings in where" $ do

    let program = [r|
f x = go base where
  base : I32
  base = x * 2
  go : I32 -> I32
  go n = n + 1
|]

    it "evals" $ runEvaluate program "f 5" `shouldReturn` "11"
