{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies        #-}

module Compile.CodeGen
  ( codeGen
  ) where

import           Common
import           Env
import           Inbuilts
import           Introspect
import           Praxis
import           Prelude    hiding (lookup, exp)
import           Print
import           Stage
import           Term

codeGen :: Annotated Program -> Praxis String
codeGen p = save stage $ do
  stage .= CodeGen
  s <- generate p
  return $ inbuiltInclude ++ "\n" ++ s

generate :: forall a. Term a => Annotated a -> Praxis String
generate x = ($ x) $ case witness :: I a of
  IProgram -> program
  IDecl -> decl
  IExp  -> exp
  IType -> ty
  _     -> extract generate

program :: Annotated Program -> Praxis String
program = extract generate -- TODO will need to forward declare functions (if they are mutually recursive)

decl :: Annotated Decl -> Praxis String
decl (a :< d) = case d of

  DeclVar n _ e -> throw "unimplemented"
  
  _ -> throw "unimplemented"


exp :: Annotated Exp -> Praxis String
exp (a :< e) = case e of

  _ -> throw "unimplemented"


ty :: Annotated Type -> Praxis String
ty (a :< t) = case t of

  _ -> throw "unimplemented"
