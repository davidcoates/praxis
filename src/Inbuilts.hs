module Inbuilts
  (
    inbuilts
  , TopDecl(..)
  ) where

import Type

data TopDecl = TopDecl { ty :: QPure, name :: String, defn :: String }

-- TODO Qualify with Prelude or Base or some other sentinel
inbuilts :: [(String, TopDecl)]
inbuilts =
  [
  ("+", TopDecl { ty = mono (TyFun (TyPrim (TyInt)) (pureTy (TyFun (TyPrim TyInt) (pureTy (TyPrim TyInt)))))
                , name = "plus"
                , defn = "auto plus = [](int x) -> { return ([](int y) -> { return x + y; }); };"
                })
  ]
