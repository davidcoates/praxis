{-# LANGUAGE QuasiQuotes #-}

module KindSpec where

import           Test.Hspec
import           Text.RawString.QQ

import           Introspect
import           Util


spec :: Spec
spec = do

  describe "subkinds" $ do

    describe "View & is a subkind of View ?" $ do

      let program = trim [r|
datatype Foo ?v a = Foo ?v a

datatype Bar &v a = Bar (Foo &v a)
  |]

      it "kind checks" $ runPretty (check ProgramT program) `shouldReturn` trim [r|
datatype unboxed Foo ?v a = [forall ?v a . ?v a -> Foo ?v a] Foo ?v a
datatype unboxed Bar &v a = [forall &v a . Foo &v a -> Bar &v a] Bar Foo &v a
|]


    describe "View ? is not a subkind of View &" $ do

      let program = trim [r|
datatype Foo &v a = Foo &v a

datatype Bar ?v a = Bar (Foo ?v a)
  |]

      it "does not kind check" $ runPretty (check ProgramT program) `shouldReturn` trim [r|
kind check error: unable to satisfy: View ≤ Ref
  | primary cause: type application [Ref -> Type -> Type] Foo ($) [View] ?v at 3:26
  | secondary causes:
  | - data type Foo with argument(s) [Ref] &v, [Type] a at 1:1
  | - type operator application [Ref] &v (★) [Type] a at 1:25
|]
