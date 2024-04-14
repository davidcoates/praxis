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
          , ("- 1 - - - 1", "(-1) - (- (-1))")
          ]

    forM_ expressions $ \(a, b) -> do
      it (show a ++ " parses like " ++ show b) $ do
        x <- parseAs IExp a
        y <- parseAs IExp b
        x `shouldBe` y
      it (show a ++ " parses idempotently") $ do
        x <- parseAs IExp a
        y <- parseAs IExp x
        x `shouldBe` y


  describe "simple types" $ do

    let types =
          [ ("Int -> Int -> Int", "Int -> (Int -> Int)")
          , ("A B C", "A (B C)")
          , ("Maybe Maybe a -> Maybe b", "(Maybe (Maybe a)) -> (Maybe b)")
          , ("forall a b. (a, b)", "forall a b . ( a, b )")
          , ("forall &r. &r Array Int -> ()", "forall &r . &r Array Int -> ()")
          , ("forall ?r. ?r Array Int -> ()", "forall ?r . ?r Array Int -> ()")
          ]

    forM_ types $ \(a, b) -> do
      it (show a ++ " parses like " ++ show b) $ do
        a <- parseAs IQType  a
        b <- parseAs IQType b
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
        t' <- parseAs IQType t
        t' `shouldBe` "1:1 error: type variables are not distinct"


  describe "do not ending in expression" $ do

    let program = trim [r|
foo = do
  let x = 1
  let y = 1
|]

    it "does not parse" $ check program `shouldReturn` "3:3 error: do block must end in an expression"


  describe "variarble redeclaration" $ do

    let program = trim [r|
fst : forall a. (a, a) -> a
fst (a, a) = a
|]

    it "does not parse" $ parse program `shouldReturn` trim [r|
2:5 error: variables are not distinct
|]


  describe "type variarble redeclaration" $ do

    let program = trim [r|
datatype Foo [a, a] = Foo a
|]

    it "does not parse" $ parse program `shouldReturn` "1:14 error: type variables are not distinct"



  describe "mixfix operators" $ do

    let program = [r|
implies : (Bool, Bool) -> Bool
implies (a, b) = b || !a

operator (_ --> _) = implies

iff : (Bool, Bool) -> Bool
iff (a, b) = (a && b) || (!a && !b)

operator (_ <-> _) = iff where
  precedence below (_ --> _)

ifthenelse : (Bool, Int, Int) -> Int
ifthenelse (c, a, b) = if c then a else b

operator (_ <?> _ <:> _) = ifthenelse where
  precedence below (_ <-> _)
|]

    it "parses" $ parse program `shouldReturn` trim [r|
implies_0 : ( Bool , Bool ) -> Bool = \ ( a_0 , b_0 ) -> or ( b_0 , not a_0 )
operator ( _ --> _ ) = implies_0
iff_0 : ( Bool , Bool ) -> Bool = \ ( a_1 , b_1 ) -> or ( and ( a_1 , b_1 ) , and ( not a_1 , not b_1 ) )
operator ( _ <-> _ ) = iff_0 where
  precedence
    below ( _ --> _ )
ifthenelse_0 : ( Bool , Int , Int ) -> Int = \ ( c_0 , a_2 , b_2 ) -> if c_0 then a_2 else b_2
operator ( _ <?> _ <:> _ ) = ifthenelse_0 where
  precedence
    below ( _ <-> _ )
|]

    it "evaluates" $ do
      interpret program "False <-> True <?> 1 <:> 0" `shouldReturn` "0"


