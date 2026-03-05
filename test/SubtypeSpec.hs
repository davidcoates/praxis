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
rec datatype List a = Nil () | Cons (a, List a)

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

    it "parses" $ runPretty (parse ProgramT program) `shouldReturn` trim [r|
rec
  datatype boxed List a = Nil ( ) | Cons ( a , List a )
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

    it "type checks" $ runPretty (check ProgramT program) `shouldReturn` trim [r|
rec
  datatype boxed List a = [forall a . ( ) -> List a] Nil ( ) | [forall a . ( a , List a ) -> List a] Cons ( a , List a )
rec
  copy : forall ?v a . ?v List a -> List ( ?v a ) = [?v List a -> List ( ?v a )] cases
    [?v List a] Nil [( )] ( ) -> [( ) -> List ( ?v a )] Nil [( )] ( )
    [?v List a] Cons ( [?v a] x , [?v List a] xs ) -> [( ?v a , List ( ?v a ) ) -> List ( ?v a )] Cons ( [?v a] x , [?v List a -> List ( ?v a )] copy [?v List a] xs )
rec
  concat : forall ?v ?w a . ( ?v List a , ?w List a ) -> List ( { ?v , ?w } a ) = [( ?v List a , ?w List a ) -> List ( { ?v , ?w } a )] cases
    ( [?v List a] Nil [( )] ( ) , [?w List a] Nil [( )] ( ) ) -> [( ) -> List ( { ?v , ?w } a )] Nil [( )] ( )
    ( [?v List a] Cons ( [?v a] x , [?v List a] xs ) , [?w List a] ys ) -> [( { ?v , ?w } a , List ( { ?v , ?w } a ) ) -> List ( { ?v , ?w } a )] Cons ( [?v a] x : { ?v , ?w } a , [( ?v List a , ?w List a ) -> List ( { ?v , ?w } a )] concat ( [?v List a] xs , [?w List a] ys ) )
    ( [?v List a] Nil [( )] ( ) , [?w List a] ys ) -> [{ ?v , ?w } List a -> List ( { ?v , ?w } a )] copy ( [?w List a] ys : { ?v , ?w } List a )
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
