{-# LANGUAGE QuasiQuotes #-}

module ParseSpec where

import           Control.Monad     (forM_)
import           Test.Hspec
import           Text.RawString.QQ

import           Introspect
import           Util


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
          , ("- 1 - - -1", "(- 1) - (- (-1))")
          ]

    forM_ expressions $ \(a, b) -> do
      it (show a ++ " parses like " ++ show b) $ do
        x <- runPretty (parse IExp a)
        y <- runPretty (parse IExp b)
        x `shouldBe` y
      it (show a ++ " parses idempotently") $ do
        x <- runPretty (parse IExp a)
        y <- runPretty (parse IExp x)
        x `shouldBe` y


  describe "simple types" $ do

    let types =
          [ ("I32 -> I32 -> I32", "I32 -> (I32 -> I32)")
          , ("A B C", "A (B C)")
          , ("Maybe Maybe a -> Maybe b", "(Maybe (Maybe a)) -> (Maybe b)")
          , ("forall a b. (a, b)", "forall a b . ( a, b )")
          , ("forall &r. &r Array I32 -> ()", "forall &r . &r Array I32 -> ()")
          , ("forall ?r. ?r Array I32 -> ()", "forall ?r . ?r Array I32 -> ()")
          ]

    forM_ types $ \(a, b) -> do
      it (show a ++ " parses like " ++ show b) $ do
        a <- runPretty (parse IQType a)
        b <- runPretty (parse IQType b)
        a `shouldBe` b

    let types =
          [ "forall r &r. ()"
          , "forall r ?r. ()"
          , "forall r r. ()"
          , "forall &r &r. ()"
          , "forall ?r ?r. ()"
          , "forall &r ?r. ()"
          ]

    forM_ types $ \t -> do
      it (show t ++ " is not valid") $ do
        t' <- runPretty (parse IQType t)
        t' `shouldBe` "parse error at 1:1: type variables are not distinct"


  describe "do not ending in expression" $ do

    let program = trim [r|
foo = do
  let x = 1
  let y = 1
|]

    it "does not parse" $ runPretty (check IProgram program) `shouldReturn` "parse error at 3:3: do block must end in an expression"


  describe "mixfix operators" $ do

    let program = [r|
implies : (Bool, Bool) -> Bool
implies (a, b) = b || !a

operator (_ --> _) = implies

iff : (Bool, Bool) -> Bool
iff (a, b) = (a && b) || (!a && !b)

operator (_ <-> _) = iff where
  precedence below (_ --> _)

ifthenelse : (Bool, I32, I32) -> I32
ifthenelse (c, a, b) = if c then a else b

operator (_ <?> _ <:> _) = ifthenelse where
  precedence below (_ <-> _)
|]

    it "parses" $ runPretty (parse IProgram program) `shouldReturn` trim [r|
implies_0 : ( Bool , Bool ) -> Bool = \ ( a_0 , b_0 ) -> or ( b_0 , not a_0 )
iff_0 : ( Bool , Bool ) -> Bool = \ ( a_1 , b_1 ) -> or ( and ( a_1 , b_1 ) , and ( not a_1 , not b_1 ) )
ifthenelse_0 : ( Bool , I32 , I32 ) -> I32 = \ ( c_0 , a_2 , b_2 ) -> if c_0 then a_2 else b_2
|]

    it "evals" $ do
      runEvaluate program "False <-> True <?> 1 <:> 0" `shouldReturn` "0"
