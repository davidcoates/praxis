module Translate.Translate
  ( run
  ) where

import           Common
import           Introspect
import           Praxis
import           Term

import qualified Data.Text                  as Text
import qualified LLVM.Codegen               as LLVM
import qualified LLVM.Codegen.IRBuilder     as LLVM
import qualified LLVM.Codegen.ModuleBuilder as LLVM

type ModuleBuilder = LLVM.ModuleBuilderT Praxis

type IRBuilder = LLVM.IRBuilderT ModuleBuilder

run :: Annotated Program -> Praxis String
run program = do
  (LLVM.Module defns1) <- use (translation . llvmModule)
  (LLVM.Module defns2) <- LLVM.runModuleBuilderT (translateProgram program)
  let module' = LLVM.Module (defns1 ++ defns2)
  translation . llvmModule .= module'
  return $ Text.unpack (LLVM.ppllvm module')
--  display program `ifFlag` debug


{-
translate :: Term a => Annotated a -> Praxis String
translate term = ($ term) $ case typeof (view value term) of
{-
  IBind     -> generateBind
  IDataCon  -> error "standalone DataCon"
  IDeclTerm -> generateDeclTerm
  IDeclType -> generateDeclType
  IExp      -> generateExp
  IPat      -> error "standalone Pat"
-}
  _         -> value (recurseTerm translate)
-}

translateProgram :: Annotated Program -> ModuleBuilder ()
translateProgram = undefined

{-
translateProgram :: Annotated Program -> ModuleBuilder ()
translateProgram (_ :< Program decls) = mapM_ translateDecl decls

translateDecl :: Annotated Decl -> ModuleBuilder LLVM.Operand
translateDecl (_ :< decl) = return undefined

translateExp :: Annotated Exp -> ModuleBuilder LLVM.Operand
translateExp (_ :< exp) = return undefined

-}

typeToUnderlying :: Annotated Type -> LLVM.Type
typeToUnderlying (_ :< ty) = undefined


typeToHandle :: Annotated Type -> LLVM.Type
typeToHandle (_ :< ty) = case ty of

  TyCon n -> case n of
    "Bool"   -> LLVM.i1
    "Char"   -> LLVM.i32
    "I8"     -> LLVM.i8
    "I16"    -> LLVM.i16
    "I32"    -> LLVM.i32
    "I64"    -> LLVM.i64
    "ISize"  -> LLVM.i64
    "U8"     -> LLVM.i8
    "U16"    -> LLVM.i16
    "U32"    -> LLVM.i32
    "U64"    -> LLVM.i64
    "USize"  -> LLVM.i64
    "String" -> error "TODO String"

  TyApply (_ :< TyCon n) ty -> case n of
    "Array" -> error "TODO Array"

  TyApply (_ :< TyView _) ty -> typeToHandle ty
