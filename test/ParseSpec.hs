{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies      #-}
{-# LANGUAGE TypeOperators     #-}

module ParseSpec where

import           Common
import           Inbuilts
import           Introspect
import qualified Parse         (parse)
import           Praxis
import           Term

import           Control.Monad (forM_)
import           Prelude       hiding (exp, unlines)
import qualified Prelude       (unlines)
import           Test.Hspec

matches a b = (a, b)

exps =
  [ "1 + 2" `matches` "1 + 2"
  , "1 + 2 + 3" `matches` "(1 + 2) + 3"
  , "1 + 2 * 3" `matches` "1 + (2 * 3)"
  , "1 - 2 - 3" `matches` "(1 - 2) - 3"
  , "1 - - 2" `matches` "1 - (- 2)"
  , "f x 1 + g y * z" `matches` "(f (x 1)) + ((g y) * z)"
  , "f x + f y + f z" `matches` "((f x) + (f y)) + (f z)"
  , "(x, y, z)" `matches` "(x, (y, z))"]

tys =
  [ "Int -> Int -> Int" `matches` "Int -> (Int -> Int)"
  , "A B C" `matches` "A (B C)"
  , "Maybe Maybe a -> Maybe b" `matches` "(Maybe (Maybe a)) -> (Maybe b)"
  ]

-- Drop trailing newline
unlines = init . Prelude.unlines

programs =
  [ unlines
      [ "fac = cases"
      , "    0 -> 1"
      , "    n -> n * fac (n - 1)"
      ] `matches`
    unlines
      [ "fac = cases"
      , "  0 -> 1"
      , "  n -> multiply_int ( n , fac subtract_int ( n , 1 ) )"
      ]
  ]


instance (Term a, x ~ Annotation a) => Show (Tag (Source, Maybe x) a) where
  show x = fold (runPrintable (pretty x) Plain)

parse :: Term a => String -> Annotated a
parse s = runInternal initialState (Parse.parse s)

unparse :: Term a => Annotated a -> String
unparse = show

spec :: Spec
spec = do
  describe "Expressions" $ do
    forM_ exps $ \(a, b) -> do
      it (a ++ " EQUALS " ++ b) $ do
        (parse a :: Annotated Exp) `shouldBe` parse b
  describe "Types" $ do
    forM_ tys $ \(a, b) -> do
      it (a ++ " EQUALS " ++ b) $ do
        (parse a :: Annotated Type) `shouldBe` parse b
  describe "Programs" $ do
    forM_ programs $ \(a, b) -> do
      it ("\n" ++ a ++ "EQUALS\n" ++ b) $ do
        (parse a :: Annotated Program) `shouldBe` parse b
      it ("\n" ++ b ++ "IS IN NORMAL FORM") $ do
         unparse (parse b :: Annotated Program) `shouldBe` b
