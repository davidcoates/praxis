module Translate
  ( translate
  , Mode(..)
  ) where

import           Common
import           Introspect
import           Praxis
import           Stage
import           Term

data Mode = NoPrelude | Prelude | PreludeWithMain

translate :: Mode -> Annotated Program -> Praxis String
translate mode program = save stage $ do
  stage .= Translate
  program <- translate' program
  display program `ifFlag` debug
  return "TODO"

{-
  let wrappedProgram = prelude ++ "namespace praxis::user {\n" ++ program ++ "\n}"
  case mode of
    NoPrelude       -> return program
    Prelude         -> return wrappedProgram
    PreludeWithMain -> requireMain >> return (wrappedProgram ++ "\nint main(){ praxis::user::main_0(std::monostate{}); }")
-}


-- type ModuleBuilder = LLVM.ModuleBuilderT Praxis

-- type IRBuilder = LLVM.IRBuilderT ModuleBuilder

translate' :: Term a => Annotated a -> Praxis (Annotated a)
translate' term = ($ term) $ case typeof (view value term) of
{-
  IBind     -> generateBind
  IDataCon  -> error "standalone DataCon"
  IDeclTerm -> generateDeclTerm
  IDeclType -> generateDeclType
  IExp      -> generateExp
  IPat      -> error "standalone Pat"
-}
  _         -> value (recurseTerm translate')


translateProgram :: Annotated Program -> Praxis ()
translateProgram = undefined

{-
translateProgram :: Annotated Program -> ModuleBuilder ()
translateProgram (_ :< Program decls) = mapM_ translateDecl decls

translateDecl :: Annotated Decl -> ModuleBuilder LLVM.Operand
translateDecl (_ :< decl) = return undefined

translateExp :: Annotated Exp -> ModuleBuilder LLVM.Operand
translateExp (_ :< exp) = return undefined

translateType :: Annotated Type -> ModuleBuilder LLVM.Type
translateType (_ :< ty) = case ty of

  TyCon n -> case n of
    "Bool"  -> return LLVM.i1
    "Char"  -> return LLVM.i32
    "I8"    -> return LLVM.i8
    "I16"   -> return LLVM.i16
    "I32"   -> return LLVM.i32
    "I64"   -> return LLVM.i64
    "ISize" -> return LLVM.i64
    "U8"    -> return LLVM.i8
    "U16"   -> return LLVM.i16
    "U32"   -> return LLVM.i32
    "U64"   -> return LLVM.i64
    "USize" -> return LLVM.i64
    _       -> error "TODO"
-}
