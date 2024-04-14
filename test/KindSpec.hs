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
datatype Foo [ ? v_0 , a_0 ] = [forall ? v_0 a_0 . ? v_0 a_0 -> Foo [ ? v_0 , a_0 ]] Foo ? v_0 a_0
datatype Bar [ & v_1 , a_1 ] = [forall & v_1 a_1 . Foo [ & v_1 , a_1 ] -> Bar [ & v_1 , a_1 ]] Bar Foo [ & v_1 , a_1 ]
|]


    describe "View ? is not a subkind of View &" $ do

      let program = trim [r|
datatype Foo [&v, a] = Foo &v a

datatype Bar [?v, a] = Bar (Foo [?v, a])
  |]

      it "does not kind check" $ check program `shouldReturn` trim [r|
error: found contradiction [3:28] View ? ≤ View & and ^k3 ≤ Type
|-> [3:28] ( View ? , ^k3 ) ≤ ( View & , Type )
|-> (type function application)
|]



