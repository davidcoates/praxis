module Translate
  ( runProgram
  , Mode(..)
  ) where

import           Common
import           Praxis
import           Stage
import           Term

import qualified Data.Text    as Text
import qualified LLVM.Codegen as LLVM


data Mode = NoPrelude | Prelude | PreludeWithMain


type ModuleBuilder = LLVM.ModuleBuilderT Praxis

type IRBuilder = LLVM.IRBuilderT ModuleBuilder

-- TODO return text
runProgram :: Mode -> Annotated Program -> Praxis String
runProgram mode program = save stage $ do
  stage .= Translate
  program <- (Text.unpack . LLVM.ppllvm) <$> LLVM.runModuleBuilderT (translateProgram program)
  display program `ifFlag` debug
  return program
{-
  let wrappedProgram = prelude ++ "namespace praxis::user {\n" ++ program ++ "\n}"
  case mode of
    NoPrelude       -> return program
    Prelude         -> return wrappedProgram
    PreludeWithMain -> requireMain >> return (wrappedProgram ++ "\nint main(){ praxis::user::main_0(std::monostate{}); }")
-}


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



