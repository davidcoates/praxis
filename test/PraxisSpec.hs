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

  describe "Simple Expressions" $ do

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
      it "parses" $ do
        (parse a :: Annotated Exp) `shouldBe` parse b
      it "parses (idempotent)" $ do
        (parse b :: Annotated Exp) `shouldBe` parse b


  describe "Simple Types" $ do


    let types =
          [ ("Int -> Int -> Int", "Int -> (Int -> Int)")
          , ("A B C", "A (B C)")
          , ("Maybe Maybe a -> Maybe b", "(Maybe (Maybe a)) -> (Maybe b)")
          ]

    forM_ types $ \(a, b) -> do
      it "parses" $ do
        (parse a :: Annotated Type) `shouldBe` parse b
      it "parses (idempotent)" $ do
        (parse b :: Annotated Type) `shouldBe` parse b


  describe "Factorial" $ do

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


  describe "Swap" $ do

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


  describe "Copy" $ do

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


  describe "Either" $ do

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
