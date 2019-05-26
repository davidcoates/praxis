module ParseSpec where

import           Annotate      (Parsed)
import           AST           (Exp)
import qualified Parse         (parse)
import           Praxis
import           Print

import           Control.Monad (forM_)
import           Test.Hspec

sources = [ ("1 + 2 * 3", "1 + (2 * 3)") ]

parse :: String -> Parsed Exp
parse s = runStatic emptyState (Parse.parse s)

spec :: Spec
spec = describe "Parse" $ do
  forM_ sources $ \(a, b) -> do
    it (a ++ " should parse as " ++ b) $ do
      parse a `shouldBe` parse b
