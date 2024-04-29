{-# LANGUAGE QuasiQuotes #-}

module IntSpec where

import           Control.Monad     (forM_)
import           Test.Hspec
import           Text.RawString.QQ

import           Util


spec :: Spec
spec = do

  describe "literals" $ do

    let
      overflows =
        [ ("256", "U8")
        , ("128", "I8")
        , ("65536", "U16")
        , ("32768", "I16")
        , ("4294967296", "U32")
        , ("2147483648", "I32")
        , ("18446744073709551616", "U64")
        , ("9223372036854775808", "I64")
        ]

    forM_ overflows $ \(number, ty) -> do
      it (number ++ " overflows " ++ ty) $ check ("x = " ++ number ++ " : " ++ ty) `shouldReturn` trim [r|
type check error: unable to satisfy: |] <> number <> " ∈ " <> ty <> [r|
  | primary cause: integer literal |] <> number <> [r| at 1:5
  | secondary cause: user-supplied signature at 1:5|]

    let
      underflows =
        [ ("-1", "U8")
        , ("-129", "I8")
        , ("-1", "U16")
        , ("-32769", "I16")
        , ("-1", "U32")
        , ("-2147483649", "I32")
        , ("-1", "U64")
        , ("-9223372036854775809", "I64")
        ]

    forM_ underflows $ \(number, ty) -> do
      it (number ++ " underflows " ++ ty) $ check ("x = " ++ number ++ " : " ++ ty) `shouldReturn` trim [r|
type check error: unable to satisfy: |] <> number <> " ∈ " <> ty <> [r|
  | primary cause: integer literal |] <> number <> [r| at 1:5
  | secondary cause: user-supplied signature at 1:5|]
