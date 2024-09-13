{-# LANGUAGE QuasiQuotes #-}

module SubtypeSpec where

import           Test.Hspec
import           Text.RawString.QQ

import           Introspect
import           Util


spec :: Spec
spec = do

  describe "view subsumption" $ do

    let program = trim [r|
datatype rec List a = Nil () | Cons (a, List a)

-- TODO this ought to be a no-op for value views
rec
  copy : forall ?v a. ?v List a -> List (?v a)
  copy = cases
    Nil ()       -> Nil ()
    Cons (x, xs) -> Cons (x, copy xs)

rec
  concat : forall ?v ?w a. (?v List a, ?w List a) -> List ({?v, ?w} a)
  concat = cases
    (Nil (), Nil ()) -> Nil ()
    (Cons (x, xs), ys) -> Cons (x : {?v, ?w} a, concat (xs, ys))
    (Nil (), ys) -> copy (ys : {?v, ?w} List a)

operator (_ ++ _) = concat where
  left associative
|]

    it "parses" $ runPretty (parse IProgram program) `shouldReturn` trim [r|
datatype rec List a = Nil ( ) | Cons ( a , List a )
rec
  copy : forall ?v a . ?v List a -> List ( ?v a ) = cases
    Nil ( ) -> Nil ( )
    Cons ( x , xs ) -> Cons ( x , copy xs )
rec
  concat : forall ?v ?w a . ( ?v List a , ?w List a ) -> List ( { ?v , ?w } a ) = cases
    ( Nil ( ) , Nil ( ) ) -> Nil ( )
    ( Cons ( x , xs ) , ys ) -> Cons ( x : { ?v , ?w } a , concat ( xs , ys ) )
    ( Nil ( ) , ys ) -> copy ( ys : { ?v , ?w } List a )
|]

    it "type checks" $ runPretty (check IProgram program) `shouldReturn` trim [r|
datatype rec List a_0 = [forall a_0 . ( ) -> List a_0] Nil ( ) | [forall a_0 . ( a_0 , List a_0 ) -> List a_0] Cons ( a_0 , List a_0 )
rec
  copy_0 : forall ?v_0 a_1 . ?v_0 List a_1 -> List ( ?v_0 a_1 ) = [?v_0 List a_1 -> List ( ?v_0 a_1 )] cases
    [?v_0 List a_1] Nil [( )] ( ) -> [( ) -> List ( ?v_0 a_1 )] Nil [( )] ( )
    [?v_0 List a_1] Cons ( [?v_0 a_1] x_0 , [?v_0 List a_1] xs_0 ) -> [( ?v_0 a_1 , List ( ?v_0 a_1 ) ) -> List ( ?v_0 a_1 )] Cons ( [?v_0 a_1] x_0 , [?v_0 List a_1 -> List ( ?v_0 a_1 )] copy_0 [?v_0 List a_1] xs_0 )
rec
  concat_0 : forall ?v_1 ?w_0 a_2 . ( ?v_1 List a_2 , ?w_0 List a_2 ) -> List ( { ?v_1 , ?w_0 } a_2 ) = [( ?v_1 List a_2 , ?w_0 List a_2 ) -> List ( { ?v_1 , ?w_0 } a_2 )] cases
    ( [?v_1 List a_2] Nil [( )] ( ) , [?w_0 List a_2] Nil [( )] ( ) ) -> [( ) -> List ( { ?v_1 , ?w_0 } a_2 )] Nil [( )] ( )
    ( [?v_1 List a_2] Cons ( [?v_1 a_2] x_1 , [?v_1 List a_2] xs_1 ) , [?w_0 List a_2] ys_0 ) -> [( { ?v_1 , ?w_0 } a_2 , List ( { ?v_1 , ?w_0 } a_2 ) ) -> List ( { ?v_1 , ?w_0 } a_2 )] Cons ( [?v_1 a_2] x_1 : { ?v_1 , ?w_0 } a_2 , [( ?v_1 List a_2 , ?w_0 List a_2 ) -> List ( { ?v_1 , ?w_0 } a_2 )] concat_0 ( [?v_1 List a_2] xs_1 , [?w_0 List a_2] ys_0 ) )
    ( [?v_1 List a_2] Nil [( )] ( ) , [?w_0 List a_2] ys_1 ) -> [{ ?v_1 , ?w_0 } List a_2 -> List ( { ?v_1 , ?w_0 } a_2 )] copy_0 ( [?w_0 List a_2] ys_1 : { ?v_1 , ?w_0 } List a_2 )
|]

    it "evals" $ do

      runEvaluate program [r|
do
  let xs = Cons (1, Cons (2, Cons (3, Nil ())))
  let ys = Cons (4, Cons (5, Cons (6, Nil ())))
  xs ++ ys
|] `shouldReturn` "Cons (1, Cons (2, Cons (3, Cons (4, Cons (5, Cons (6, Nil ()))))))"

      runEvaluate program [r|
do
  let xs = Cons (1, Cons (2, Cons (3, Nil ())))
  let ys = Cons (4, Cons (5, Cons (6, Nil ())))
  &xs ++ ys
|] `shouldReturn` "Cons (1, Cons (2, Cons (3, Cons (4, Cons (5, Cons (6, Nil ()))))))"

      runEvaluate program [r|
do
  let xs = Cons (1, Cons (2, Cons (3, Nil ())))
  let ys = Cons (4, Cons (5, Cons (6, Nil ())))
  xs ++ &ys
|] `shouldReturn` "Cons (1, Cons (2, Cons (3, Cons (4, Cons (5, Cons (6, Nil ()))))))"

      runEvaluate program [r|
do
  let xs = Cons (1, Cons (2, Cons (3, Nil ())))
  let ys = Cons (4, Cons (5, Cons (6, Nil ())))
  &xs ++ &ys
|] `shouldReturn` "Cons (1, Cons (2, Cons (3, Cons (4, Cons (5, Cons (6, Nil ()))))))"
