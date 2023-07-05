{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies      #-}
{-# LANGUAGE TypeOperators     #-}
{-# LANGUAGE QuasiQuotes       #-}

module PraxisSpec where

import Text.RawString.QQ

import           Common
import           Inbuilts
import           Introspect
import qualified Parse         (parse)
import qualified Check         (check)
import qualified Interpret     (interpret)
import           Value (Value(..))
import           Praxis
import           Print
import           Term

import           Control.Monad (forM_)
import           Prelude       hiding (exp, unlines)
import qualified Prelude       (unlines)
import           Test.Hspec

instance (Term a, x ~ Annotation a) => Show (Tag (Source, Maybe x) a) where
  show x = fold (runPrintable (pretty x) Types)

parse :: Term a => String -> Annotated a
parse s = runInternal initialState (Parse.parse s)

check :: Term a => String -> Annotated a
check s = runInternal initialState (Parse.parse s >>= Check.check)

interpret :: String -> String -> String
interpret program exp = runInternal initialState $ do
    Interpret.interpret program :: Praxis (Annotated Program, ())
    (_, v) <- Interpret.interpret exp :: Praxis (Annotated Exp, Value)
    return (show v)

-- Drop trailing newline
unlines = init . Prelude.unlines

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
      it (show a ++ " parses") $ do
        (parse a :: Annotated Exp) `shouldBe` parse b
      it (show b ++ " parses (idempotent)") $ do
        (parse b :: Annotated Exp) `shouldBe` parse b


  describe "simple types" $ do

    let types =
          [ ("Int -> Int -> Int", "Int -> (Int -> Int)")
          , ("A B C", "A (B C)")
          , ("Maybe Maybe a -> Maybe b", "(Maybe (Maybe a)) -> (Maybe b)")
          ]

    forM_ types $ \(a, b) -> do
      it (show a ++ " parses") $ do
        (parse a :: Annotated Type) `shouldBe` parse b
      it (show b ++ " parses (idempotent)") $ do
        (parse b :: Annotated Type) `shouldBe` parse b


  describe "simple programs" $ do

    describe "factorial (recursion)" $ do

      let program = unlines
            [ "fac = cases"
            , "  0 -> 1"
            , "  n -> n * fac (n - 1)"
            ]

      it "type checks" $ do
        show (check program :: Annotated Program) `shouldBe` unlines
          [ "fac = [Int -> Int] cases"
          , "  [Int] 0 -> [Int] 1"
          , "  [Int] n -> [Int] [( Int , Int ) -> Int] multiply_int [( Int , Int )] ( [Int] n , [Int] [Int -> Int] fac [( Int , Int ) -> Int] subtract_int [( Int , Int )] ( [Int] n , [Int] 1 ) )"
          ]

      it "evaluates" $ do
        interpret program "fac 0"  `shouldBe` "1"
        interpret program "fac 5"  `shouldBe` "120"
        interpret program "fac 15" `shouldBe` "1307674368000"


    describe "swap (polymorphic function)" $ do

      let program = unlines
            [ "swap : forall a b. (a, b) -> (b, a)"
            , "swap (a, b) = (b, a)"
            ]

      it "type checks" $ do
        show (check program :: Annotated Program) `shouldBe` unlines
          [ "swap : forall 't0 't1 . ( 't0 , 't1 ) -> ( 't1 , 't0 ) = [( 't0 , 't1 ) -> ( 't1 , 't0 )] \\ [( 't0 , 't1 )] ( ['t0] a , ['t1] b ) -> [( 't1 , 't0 )] ( ['t1] b , ['t0] a )"
          ]

      it "evaulates" $ do
        interpret program "swap (0, 1)"      `shouldBe` "(1, 0)"
        interpret program "swap (True, 1)"   `shouldBe` "(1, True)"
        interpret program "swap (1, 2, 3)"   `shouldBe` "((2, 3), 1)"
        interpret program "swap ((2, 3), 1)" `shouldBe` "(1, (2, 3))"
        -- interpret program "swap (\"abc\", 0)" `shouldBe` "(0, \"abc\")"


    describe "copy (polymorphic function with constraint)" $ do

      let program = unlines
            [ "copy : forall a. [Share a] => a -> (a, a)"
            , "copy x = (x, x)"
            ]

      it "type checks" $ do
        show (check program :: Annotated Program) `shouldBe` unlines
          [ "copy : forall 't0 . [ Share 't0 ] => 't0 -> ( 't0 , 't0 ) = ['t0 -> ( 't0 , 't0 )] \\ ['t0] x -> [( 't0 , 't0 )] ( ['t0] x , ['t0] x )"
          ]

      it "evaulates" $ do
        interpret program "copy 0"         `shouldBe` "(0, 0)"
        interpret program "copy (0, True)" `shouldBe` "((0, True), (0, True))"


    describe "Either (polymorphic data type)" $ do

      let program = unlines
            [ "type Either [a, b] = cases"
            , "    Left a"
            , "    Right b"
            ]

      it "type checks" $ do
        show (check program :: Annotated Program) `shouldBe` unlines
          [ "type Either [ a , b ] = cases"
          , "  [forall a b . a -> Either [ a , b ]] Left a"
          , "  [forall a b . b -> Either [ a , b ]] Right b"
          ]

      it "evaulates" $ do
        interpret program "Left 0"  `shouldBe` "Left 0"
        interpret program "Right 1" `shouldBe` "Right 1"


  describe "complex programs" $ do

    describe "mutual recursion" $ do

      let program = unlines
            [ "f = cases"
            , "  0 -> 1"
            , "  n -> n - m f (n - 1)"
            , ""
            , "m = cases"
            , "  0 -> 0"
            , "  n -> n - f m (n - 1)"
            ]

      it "type checks" $ do
        show (check program :: Annotated Program) `shouldBe` unlines
          [ "f = [Int -> Int] cases"
          , "  [Int] 0 -> [Int] 1"
          , "  [Int] n -> [Int] [( Int , Int ) -> Int] subtract_int [( Int , Int )] ( [Int] n , [Int] [Int -> Int] m [Int -> Int] f [( Int , Int ) -> Int] subtract_int [( Int , Int )] ( [Int] n , [Int] 1 ) )"
          , "m = [Int -> Int] cases"
          , "  [Int] 0 -> [Int] 0"
          , "  [Int] n -> [Int] [( Int , Int ) -> Int] subtract_int [( Int , Int )] ( [Int] n , [Int] [Int -> Int] f [Int -> Int] m [( Int , Int ) -> Int] subtract_int [( Int , Int )] ( [Int] n , [Int] 1 ) )"
          ]

      it "evaluates" $ do
        interpret program "f 0" `shouldBe` "1"
        interpret program "f 1" `shouldBe` "1"
        interpret program "f 2" `shouldBe` "2"
        interpret program "f 3" `shouldBe` "2"
        interpret program "f 4" `shouldBe` "3"
        interpret program "f 5" `shouldBe` "3"
        interpret program "f 6" `shouldBe` "4"
        interpret program "m 0" `shouldBe` "0"
        interpret program "m 1" `shouldBe` "0"
        interpret program "m 2" `shouldBe` "1"
        interpret program "m 3" `shouldBe` "2"
        interpret program "m 4" `shouldBe` "2"
        interpret program "m 5" `shouldBe` "3"
        interpret program "m 6" `shouldBe` "4"


    describe "list (quantified type operators)" $ do

      let program = unlines
            [ "type List a = cases"
            , "  Nil"
            , "  Cons (a, List a)"
            , ""
            , "map : forall ?v a b. (?v a -> b) -> ?v List a -> List b"
            , "map f = cases"
            , "  Nil          -> Nil"
            , "  Cons (x, xs) -> Cons (f x, (map f) xs)"
            , ""
            , "sum : &List Int -> Int"
            , "sum = cases"
            , "  Nil          -> 0"
            , "  Cons (x, xs) -> x + sum xs"
            ]

      it "type checks" $ do
        show (check program :: Annotated Program) `shouldBe` unlines
          [ "type List a = cases"
          , "  [forall a . List a] Nil"
          , "  [forall a . ( a , List a ) -> List a] Cons ( a , List a )"
          , "map : forall ?'o0 't0 't1 . ( ?'o0 't0 -> 't1 ) -> ?'o0 List 't0 -> List 't1 = [( ?'o0 't0 -> 't1 ) -> ?'o0 List 't0 -> List 't1] \\ [?'o0 't0 -> 't1] f -> [?'o0 List 't0 -> List 't1] cases"
          , "  [?'o0 List 't0] Nil -> [List 't1] Nil"
          , "  [?'o0 List 't0] Cons [?'o0 ( 't0 , List 't0 )] ( [?'o0 't0] x , [?'o0 List 't0] xs ) -> [List 't1] [( 't1 , List 't1 ) -> List 't1] Cons [( 't1 , List 't1 )] ( ['t1] [?'o0 't0 -> 't1] f [?'o0 't0] x , [List 't1] [?'o0 List 't0 -> List 't1] ( [( ?'o0 't0 -> 't1 ) -> ?'o0 List 't0 -> List 't1] map [?'o0 't0 -> 't1] f ) [?'o0 List 't0] xs )"
          , "sum : & List Int -> Int = [& List Int -> Int] cases"
          , "  [& List Int] Nil -> [Int] 0"
          , "  [& List Int] Cons [& ( Int , List Int )] ( [Int] x , [& List Int] xs ) -> [Int] [( Int , Int ) -> Int] add_int [( Int , Int )] ( [Int] x , [Int] [& List Int -> Int] sum [& List Int] xs )"
          ]

      it "evaulates" $ do
        interpret program "let xs = Cons (1, Cons (2, Cons (3, Nil))) in sum &xs" `shouldBe` "6"
        interpret program "let xs = Cons (1, Cons (2, Cons (3, Nil))) in let ys = (map (\\x -> x * 2)) &xs in sum &ys" `shouldBe` "12"


    describe "shadowing" $ do

      let program = unlines
            [ "f x = f x where"
            , "  f : Int -> Int"
            , "  f x = x"
            , ""
            , "g x = f x where"
            , "  f = cases"
            , "    0 -> 1"
            , "    n -> f (n - 1) * n"
            ]

      it "type checks" $ do
        show (check program :: Annotated Program) `shouldBe` unlines
          [ "f = [Int -> Int] \\ [Int] x -> [Int] [Int] [Int -> Int] f [Int] x where"
          , "  f : Int -> Int = [Int -> Int] \\ [Int] x -> [Int] x"
          , "g = [Int -> Int] \\ [Int] x -> [Int] [Int] [Int -> Int] f [Int] x where"
          , "  f = [Int -> Int] cases"
          , "    [Int] 0 -> [Int] 1"
          , "    [Int] n -> [Int] [( Int , Int ) -> Int] multiply_int [( Int , Int )] ( [Int] [Int -> Int] f [( Int , Int ) -> Int] subtract_int [( Int , Int )] ( [Int] n , [Int] 1 ) , [Int] n )"
          ]

      it "evaulates" $ do
        interpret program "f 5" `shouldBe` "5"
        interpret program "g 5" `shouldBe` "120"
