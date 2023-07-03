{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies      #-}
{-# LANGUAGE TypeOperators     #-}

module CheckSpec where

import           Common
import           Inbuilts
import           Introspect
import qualified Parse         (parse)
import qualified Check         (check)
import           Praxis
import           Print
import           Term

import           Control.Monad (forM_)
import           Prelude       hiding (exp, unlines)
import qualified Prelude       (unlines)
import           Test.Hspec

matches a b = (a, b)

-- Drop trailing newline
unlines = init . Prelude.unlines

programs =
  [ unlines
      [ "fac = cases"
      , "    0 -> 1"
      , "    n -> n * fac (n - 1)"
      ] `matches`
    unlines
      [ "fac = [Int -> Int] cases"
      , "  [Int] 0 -> [Int] 1"
      , "  [Int] n -> [Int] [( Int , Int ) -> Int] multiply_int [( Int , Int )] ( [Int] n , [Int] [Int -> Int] fac [( Int , Int ) -> Int] subtract_int [( Int , Int )] ( [Int] n , [Int] 1 ) )"
      ]
  , unlines
      [ "swap : forall a b. (a, b) -> (b, a)"
      , "swap (a, b) = (b, a)"
      ] `matches`
    unlines
      [ "swap : forall 't0 't1 . ( 't0 , 't1 ) -> ( 't1 , 't0 ) = [( 't0 , 't1 ) -> ( 't1 , 't0 )] \\ [( 't0 , 't1 )] ( ['t0] a , ['t1] b ) -> [( 't1 , 't0 )] ( ['t1] b , ['t0] a )" ]
  , unlines
      [ "copy : forall a. [Share a] => a -> (a, a)"
      , "copy x = (x, x)"
      ] `matches`
    unlines
      [ "copy : forall 't0 . [ Share 't0 ] => 't0 -> ( 't0 , 't0 ) = ['t0 -> ( 't0 , 't0 )] \\ ['t0] x -> [( 't0 , 't0 )] ( ['t0] x , ['t0] x )" ]
  ]


instance (Term a, x ~ Annotation a) => Show (Tag (Source, Maybe x) a) where
  show x = fold (runPrintable (pretty x) Types)

check :: Term a => String -> Annotated a
check s = runInternal initialState (Parse.parse s >>= Check.check)

spec :: Spec
spec = do
  describe "Programs" $ do
    forM_ programs $ \(a, b) -> do
      it ("\n" ++ a ++ "EQUALS\n" ++ b) $ do
        show (check a :: Annotated Program) `shouldBe` b
