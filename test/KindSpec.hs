{-# LANGUAGE QuasiQuotes #-}

module KindSpec where

import           Test.Hspec
import           Text.RawString.QQ

import           Util


spec :: Spec
spec = do

  describe "subkinds" $ do

    describe "View & is a subkind of View ?" $ do

      let program = trim [r|
datatype Foo [?v, a] = Foo ?v a

datatype Bar [&v, a] = Bar (Foo [&v, a])
  |]

      it "kind checks" $ check program `shouldReturn` trim [r|
datatype unboxed Foo [ ? v_0 , a_0 ] = [forall ? v_0 a_0 . ? v_0 a_0 -> Foo [ ? v_0 , a_0 ]] Foo ? v_0 a_0
datatype unboxed Bar [ & v_1 , a_1 ] = [forall & v_1 a_1 . Foo [ & v_1 , a_1 ] -> Bar [ & v_1 , a_1 ]] Bar Foo [ & v_1 , a_1 ]
|]


    describe "View ? is not a subkind of View &" $ do

      let program = trim [r|
datatype Foo [&v, a] = Foo &v a

datatype Bar [?v, a] = Bar (Foo [?v, a])
  |]

      it "does not kind check" $ check program `shouldReturn` trim [r|
kind check error: unable to satisfy: View ? ≤ View &
  | derived from: ( View ? , ^k3 ) ≤ ( View & , Type )
  | primary cause: type application [( View & , Type ) -> Type] Foo ($) [ [View ?] ? v_1 , [^k3] a_1 ] at 3:28
  | secondary causes:
  | - data type Foo [ [View &] & v_0 , [Type] a_0 ] at 1:1
  | - type application [View &] & v_0 ($) [Type] a_0 at 1:28
|]
