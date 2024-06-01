{-# LANGUAGE GADTs #-}

module Core.Mono
  ( run
  ) where

import           Common
import           Core.State
import           Introspect
import           Praxis
import           Stage
import           Term


{-|
  All polymorphic terms and types are specialised, so that the monod tree is completely monomorphic with no type variables.

  The following constructs are eliminated:
  - SpecialiseDetail
-}

-- TODO !

run :: Term a => Annotated a -> Praxis (Annotated a)
run term = do
  term <- mono term
  display "monomorphised term" term `ifFlag` debug
  return term

mono :: Term a => Annotated a -> Praxis (Annotated a)
mono term = ($ term) $ case typeof (view value term) of
  _ -> value (recurseTerm mono) -- TODO

mangleName :: Name -> Name
mangleName name = "_" ++ show (length name) ++ name

mangleType :: Annotated Type -> Name
mangleType (a :< ty) = case ty of

  TypeApplyOp _ t2 -> mangleType t2

  TypeApply t1 t2 -> mangleType t2 ++ mangleType t1 ++ "A"

  TypeCon name -> mangleName name

  TypeFn t1 t2 -> mangleType t2 ++ mangleType t1 ++ "F"

  TypePair t1 t2 -> mangleType t1 ++ mangleType t2 ++ "P"

  TypeUnit -> "U"


specialisedName :: Name -> [Annotated Type] -> Name
specialisedName name tys = mangleName name ++ concat [ mangleType ty | ty <- tys ]
