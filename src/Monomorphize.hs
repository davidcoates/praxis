{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE UndecidableInstances #-}

module Monomorphize
  ( run
  , Monomorphization(..)
  ) where

import           Common
import           Introspect
import           Monomorphize.State
import           Praxis
import           Stage
import           Term


type family Monomorphization a where
  Monomorphization Program = Annotated Monomorphize Program
  Monomorphization Exp = (Annotated Monomorphize Program, Annotated Monomorphize Exp)

run :: IsTerm a => Annotated TypeCheck a -> Praxis (Monomorphization a)
run term = monomorphize term

monomorphize :: IsTerm a => Annotated TypeCheck a -> Praxis (Monomorphization a)
monomorphize term = case typeof (view value term) of

  ExpT -> do
    exp <- monomorphizeExp term
    program <- getProgram
    return (program, exp)

  ProgramT -> do
    () <- monomorphizeProgram term
    program <- getProgram
    return program

  where
    getProgram :: Praxis (Annotated Monomorphize Program)
    getProgram = do
      decls <- use (monomorphizeState . exportedDecls)
      monomorphizeState . exportedDecls .= []
      return (phantom (Program decls))

{-
mangleName :: Name -> Name
mangleName name = "_" ++ show (length name) ++ name

mangleType :: Annotated Type -> Name
mangleType (_ :< ty) = case ty of

  TypeApplyOp t1 t2 -> mangleType t1 ++ mangleType t2

  TypeApply t1 t2   -> "A" ++ mangleType t2 ++ mangleType t1

  TypeCon name      -> mangleName name

  TypeFn t1 t2      -> "F" ++ mangleType t2 ++ mangleType t1

  TypePair t1 t2    -> "P" ++ mangleType t1 ++ mangleType t2

  TypeUnit          -> "U"

  TypeIdentityOp    -> ""

  TypeSetOp _       -> "R"

  TypeRef _         -> "R"


specialisedName :: Name -> [Annotated Type] -> Name
specialisedName name tys = mangleName name ++ concat [ mangleType ty | ty <- tys ]
-}

monomorphizeExp :: Annotated TypeCheck Exp -> Praxis (Annotated Monomorphize Exp)
monomorphizeExp exp = return exp -- FIXME!

monomorphizeProgram :: Annotated TypeCheck Program -> Praxis ()
monomorphizeProgram (_ :< Program decls) = do
  -- FIXME!
  monomorphizeState . exportedDecls %= (++ decls)
  return ()
