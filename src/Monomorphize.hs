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

import           Data.Map.Strict    (Map)
import qualified Data.Map.Strict    as Map


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
    display Monomorphize "monomorphized program" program `ifFlag` debug
    display Monomorphize "monomorphized exp" exp `ifFlag` debug
    return (program, exp)

  ProgramT -> do
    monomorphizeProgram term
    program <- getProgram
    display Monomorphize "monomorphized program" program `ifFlag` debug
    return program

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
monomorphizeExp ((src, ty) :< exp) = case exp of

  Capture captures inner -> do
    inner' <- castTerm inner
    captures' <- traverse (\(n, qt) -> (n,) <$> castTerm qt) captures
    return ((src, ty) :< Capture captures' inner')

  Specialize inner spec -> case view value inner of
    -- User-defined polymorphic function: generate/look up the monomorphic version
    Var name -> do
      srcDecl <- (monomorphizeState . sourceDecls) `uses` Map.lookup name
      case srcDecl of
        Just _  -> do
          monoName <- specialize name spec
          return ((src, ty) :< Var monoName)
        -- Not in sourceDecls (inbuilt or constructor): keep Specialize as-is
        Nothing -> passThrough
    -- Constructor specialization: keep as-is for now (data type mono comes later)
    _ -> passThrough
    where
      passThrough = do
        inner' <- castTerm inner
        spec'  <- traverse (\(p, t) -> (,) <$> castTerm p <*> castTerm t) spec
        return ((src, ty) :< Specialize inner' spec')

  _ -> ((src, ty) :<) <$> recurseTerm castTerm exp

-- | Normalize a specialization for use as a deduplication key.
-- Reference labels and view labels only matter to the type checker (lifetime analysis);
-- for code generation all refs are equivalent (non-null pointer), and views are either
-- ref or value. So collapse all TypeRef labels to a canonical one, and treat all
-- concrete ref-flavored views identically.
normalizeSpec :: Specialization TypeCheck -> Specialization TypeCheck
normalizeSpec = map normPair
  where
    canonicalRef = phantom (TypeRef (mkName "r"))
    normPair (pat, ty) = case view value pat of
      TypePatVar Ref _  -> (pat, canonicalRef)
      TypePatVar View _ -> case view value ty of
        TypeRef _ -> (pat, canonicalRef)
        _         -> (pat, ty)
      _                 -> (pat, ty)

-- | Look up or create the monomorphic name for a specialization of a user-defined function.
specialize :: Name -> Specialization TypeCheck -> Praxis Name
specialize name spec = do
  let spec'  = normalizeSpec spec
      types  = map snd spec'
  existing <- (monomorphizeState . instances) `uses` Map.lookup (name, types)
  case existing of
    Just monoName -> return monoName
    Nothing -> do
      monoName <- freshVar name
      -- Register before processing body to handle recursive self-calls
      monomorphizeState . instances %= Map.insert (name, types) monoName
      Just srcDecl <- (monomorphizeState . sourceDecls) `uses` Map.lookup name
      monoDecl <- specializeDeclTerm monoName spec' srcDecl
      monomorphizeState . exportedDecls %= (++ [monoDecl])
      return monoName

-- | Produce a monomorphic DeclTermVar by substituting the specialization into a polymorphic definition.
specializeDeclTerm :: Name -> Specialization TypeCheck -> Annotated TypeCheck DeclTerm -> Praxis (Annotated Monomorphize Decl)
specializeDeclTerm monoName spec (_ :< DeclTermVar _ qTy bodyExp) = do
  let monoTy = fmap (\qt -> case view value qt of
        Forall _ _ ty -> phantom (Mono (applySpec spec ty))
        Mono ty       -> phantom (Mono ty)) qTy
  monoBody <- monomorphizeExp (applySpec spec bodyExp)
  monoQTy  <- traverse castTerm monoTy
  return (phantom (DeclTerm (phantom (DeclTermVar monoName monoQTy monoBody))))

monomorphizeProgram :: Annotated TypeCheck Program -> Praxis ()
monomorphizeProgram (_ :< Program decls) = do
  mapM_ collect decls
  mapM_ emit decls
  where
    -- First pass: populate sourceDecls with polymorphic definitions
    collect :: Annotated TypeCheck Decl -> Praxis ()
    collect (_ :< decl) = case decl of
      DeclTerm dt -> collectDeclTerm dt
      DeclRec ds  -> mapM_ collectDeclRec ds
      _           -> return ()

    collectDeclRec :: Annotated TypeCheck DeclRec -> Praxis ()
    collectDeclRec (_ :< DeclRecTerm dt) = collectDeclTerm dt
    collectDeclRec _                     = return ()

    collectDeclTerm :: Annotated TypeCheck DeclTerm -> Praxis ()
    collectDeclTerm dt = case view value dt of
      DeclTermVar name (Just qt) _
        | (_ :< Forall _ _ _) <- qt -> monomorphizeState . sourceDecls %= Map.insert name dt
      _ -> return ()

    -- Second pass: emit non-polymorphic declarations
    emit :: Annotated TypeCheck Decl -> Praxis ()
    emit ann = case view value ann of
      DeclTerm dt | isPolymorphic dt -> return ()
      DeclRec ds  | any (isPolyRec . view value) ds -> return ()
      _ -> do
        monoDecl <- castTerm ann
        monomorphizeState . exportedDecls %= (++ [monoDecl])

    isPolymorphic :: Annotated TypeCheck DeclTerm -> Bool
    isPolymorphic (_ :< DeclTermVar _ (Just (_ :< Forall _ _ _)) _) = True
    isPolymorphic _                                                 = False

    isPolyRec :: DeclRec TypeCheck -> Bool
    isPolyRec (DeclRecTerm dt) = isPolymorphic dt
    isPolyRec _                = False
