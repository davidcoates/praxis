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
    monomorphizeProgram term
    getProgram

  where
    getProgram :: Praxis (Annotated Monomorphize Program)
    getProgram = do
      decls <- use (monomorphizeState . exportedDecls)
      monomorphizeState . exportedDecls .= []
      return (phantom (Program decls))

-- | Apply a specialization as a type-variable substitution over any term.
-- Replaces each TypeVar whose name appears in the specialization with the corresponding concrete type.
applySpec :: IsTerm a => Specialization TypeCheck -> Annotated TypeCheck a -> Annotated TypeCheck a
applySpec spec = sub (embedSub f)
  where
    mapping = [ (n, ty) | (_ :< TypePatVar _ n, ty) <- spec ]
    f :: Annotated TypeCheck Type -> Maybe (Annotated TypeCheck Type)
    f (_ :< TypeVar _ n) = lookup n mapping
    f _                  = Nothing

-- | Cross-stage traversal from TypeCheck to Monomorphize.
-- Must enumerate each case so GHC can reduce the Annotation type family.
castTerm :: forall a. IsTerm a => Annotated TypeCheck a -> Praxis (Annotated Monomorphize a)
castTerm term = ($ term) $ case typeof (view value term) of
  -- Exp: dispatches to monomorphizeExp for Specialize elimination
  ExpT            -> monomorphizeExp
  -- All remaining nodes: annotation is () or same type on both sides
  BindT           -> auto
  DataConT        -> auto
  DeclT           -> auto
  PatT            -> auto
  DeclRecT        -> auto
  DeclTermT       -> auto
  DeclTypeT       -> auto
  OpT             -> auto
  OpRulesT        -> auto
  PrecT           -> auto
  ProgramT        -> auto
  QTypeT          -> auto
  StmtT           -> auto
  TokT            -> auto
  TypeConstraintT -> auto
  TypePatT        -> auto
  TypeT           -> auto
  ty              -> error ("castTerm: unexpected term type " ++ show ty)
  where
    auto :: (IsTerm a, Annotation TypeCheck a ~ Annotation Monomorphize a)
         => Annotated TypeCheck a -> Praxis (Annotated Monomorphize a)
    auto = value (recurseTerm castTerm)

monomorphizeExp :: Annotated TypeCheck Exp -> Praxis (Annotated Monomorphize Exp)
monomorphizeExp ((src, ty) :< exp) = ((src, ty) :<) <$> recurseTerm castTerm exp

monomorphizeProgram :: Annotated TypeCheck Program -> Praxis ()
monomorphizeProgram _ = error "TODO: monomorphizeProgram"
