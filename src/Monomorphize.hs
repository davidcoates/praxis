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
import           Data.Maybe         (fromJust)
import           Data.Set           (Set)
import qualified Data.Set           as Set

import           Control.Monad      (forM, forM_)
import           Data.List          (partition)


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
      decls <- use (monomorphizeState . outputDecls)
      monomorphizeState . outputDecls .= []
      return (phantom (Program decls))

-- | Apply a substitution over any term.
-- Replaces each TypeVar whose name appears in the substitution with the corresponding concrete type.
applySubst :: IsTerm a => Substitution TypeCheck -> Annotated TypeCheck a -> Annotated TypeCheck a
applySubst subst = sub (embedSub f)
  where
    mapping = [ (n, ty) | (_ :< TypePatVar _ n, ty) <- subst ]
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
  PatT            -> monomorphizePat
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
  ty              -> error (show ty)
  where
    auto :: (IsTerm a, Annotation TypeCheck a ~ Annotation Monomorphize a)
         => Annotated TypeCheck a -> Praxis (Annotated Monomorphize a)
    auto = value (recurseTerm castTerm)

monomorphizeExp :: Annotated TypeCheck Exp -> Praxis (Annotated Monomorphize Exp)
monomorphizeExp ((src, ty) :< exp) = case exp of

  Specialize inner subst -> case view value inner of

    Var name -> do
      monoName <- specialize name subst
      return ((src, ty) :< Var monoName)

    Con name -> do
      Just dataName <- (monomorphizeState . conToDataType) `uses` Map.lookup name
      _ <- specializeDataType dataName subst
      let monoTypes = map snd (normalizeSubst subst)
      Just monoConName <- (monomorphizeState . specializations) `uses` Map.lookup (name, monoTypes)
      return ((src, ty) :< Con monoConName)

    Inbuilt _ -> ((src, ty) :<) <$> recurseTerm castTerm exp

  Where body decls -> do
    let (wherePolyDecls, whereMonoDecls) = partition isPolymorphic decls
        newLocalPolyNames = Set.fromList [ name | (_ :< DeclTermVar name _ _) <- wherePolyDecls ]
    savedPolyDecls  <- use (monomorphizeState . polyDecls)
    savedPolyNames  <- use (monomorphizeState . localPolyNames)
    savedPending    <- use (monomorphizeState . localPendingDecls)
    forM_ wherePolyDecls $ \dt -> case view value dt of
      DeclTermVar name _ _ -> monomorphizeState . polyDecls %= Map.insert name dt
      _                    -> return ()
    monomorphizeState . localPolyNames    %= Set.union newLocalPolyNames
    monomorphizeState . localPendingDecls .= []
    whereMonoDecls' <- traverse castTerm whereMonoDecls
    monoBody        <- monomorphizeExp body
    pending         <- use (monomorphizeState . localPendingDecls)
    monomorphizeState . polyDecls         .= savedPolyDecls
    monomorphizeState . localPolyNames    .= savedPolyNames
    monomorphizeState . localPendingDecls .= savedPending
    return ((src, ty) :< Where monoBody (pending ++ whereMonoDecls'))

  _ -> ((src, ty) :<) <$> recurseTerm castTerm exp

isPolymorphic :: Annotated TypeCheck DeclTerm -> Bool
isPolymorphic (_ :< DeclTermVar _ (Just (_ :< Poly _ _ _)) _) = True
isPolymorphic _                                               = False

-- | Normalize a substitution for use as a deduplication key.
-- Reference labels and view labels only matter to the type checker (lifetime analysis);
-- for code generation all refs are equivalent (non-null pointer), and views are either
-- ref or value. So collapse all TypeRef labels to a canonical one, and treat all
-- concrete ref-flavored views identically.
normalizeSubst :: Substitution TypeCheck -> Substitution TypeCheck
normalizeSubst = map normPair
  where
    canonicalRef = phantom (TypeRef (mkName "r"))
    normPair (pat, ty) = case view value pat of
      TypePatVar Ref _  -> (pat, canonicalRef)
      TypePatVar View _ -> case view value ty of
        TypeRef _ -> (pat, canonicalRef)
        _         -> (pat, ty)
      _                 -> (pat, ty)

-- | Strip view-application wrappers (TypeApplyOp) from the outermost type.
stripViews :: Annotated s Type -> Annotated s Type
stripViews (_ :< TypeApplyOp _ t) = stripViews t
stripViews t                      = t

-- | Decompose a type application chain into its head constructor and arguments.
-- Returns Nothing if the head is not a TypeCon.
unapplyTypeCon :: Annotated s Type -> Maybe (Name, [Annotated s Type])
unapplyTypeCon = go []
  where
    go args (_ :< TypeApply f x) = go (x : args) f
    go args (_ :< TypeCon name)  = Just (name, args)
    go _    _                    = Nothing

-- | Look up or create the monomorphic name for a specialization of a user-defined function.
specialize :: Name -> Substitution TypeCheck -> Praxis Name
specialize name subst = do
  let subst' = normalizeSubst subst
      types  = map snd subst'
  existing <- (monomorphizeState . specializations) `uses` Map.lookup (name, types)
  case existing of
    Just monoName -> return monoName
    Nothing -> do
      monoName <- freshVar name
      -- Register before processing body to handle recursive self-calls
      monomorphizeState . specializations %= Map.insert (name, types) monoName
      Just polyDecl <- (monomorphizeState . polyDecls) `uses` Map.lookup name
      isLocal <- (monomorphizeState . localPolyNames) `uses` Set.member name
      monoDecl <- specializeDeclTerm monoName subst' polyDecl
      if isLocal
        then do
          let (_ :< DeclTerm dt) = monoDecl
          monomorphizeState . localPendingDecls %= (++ [dt])
        else
          monomorphizeState . outputDecls %= (++ [monoDecl])
      return monoName

-- | Produce a monomorphic DeclTermVar by substituting the specialization into a polymorphic definition.
specializeDeclTerm :: Name -> Substitution TypeCheck -> Annotated TypeCheck DeclTerm -> Praxis (Annotated Monomorphize Decl)
specializeDeclTerm monoName subst (_ :< DeclTermVar _ qTy bodyExp) = do
  let monoTy = fmap (\qt -> case view value qt of
        Poly _ _ ty -> phantom (Mono (applySubst subst ty))
        Mono ty     -> phantom (Mono ty)) qTy
  monoBody <- monomorphizeExp (applySubst subst bodyExp)
  monoQTy  <- traverse castTerm monoTy
  return (phantom (DeclTerm (phantom (DeclTermVar monoName monoQTy monoBody))))

-- | Look up or create the monomorphic name for a specialization of a polymorphic data type.
specializeDataType :: Name -> Substitution TypeCheck -> Praxis Name
specializeDataType dataName subst = do
  let subst' = normalizeSubst subst
      types  = map snd subst'
  existing <- (monomorphizeState . specializations) `uses` Map.lookup (dataName, types)
  case existing of
    Just monoDataName -> return monoDataName
    Nothing -> do
      Just polyDecl <- (monomorphizeState . polyDataDecls) `uses` Map.lookup dataName
      let (_ :< DeclTypeData mode _ typePats cons) = polyDecl

      -- Register mono data type name FIRST (before processing body, handles recursion)
      monoDataName <- freshVar dataName
      monomorphizeState . specializations %= Map.insert (dataName, types) monoDataName

      -- Register a mono name for each constructor
      monoConNames <- forM cons $ \(_ :< DataCon conName _) -> do
        monoConName <- freshVar conName
        monomorphizeState . specializations %= Map.insert (conName, types) monoConName
        return monoConName

      -- Apply type-variable substitution to the whole DeclTypeData body
      let specData = applySubst subst' polyDecl

      -- Build a type-rewriting function: TypeApply (TypeCon n) args -> TypeCon monoN
      specializationMap <- use (monomorphizeState . specializations)
      let rewriteTy :: Annotated TypeCheck Type -> Maybe (Annotated TypeCheck Type)
          rewriteTy ty = case unapplyTypeCon ty of
            Just (n, args) ->
              let normalizedArgs = map snd (normalizeSubst (zip typePats args))
              in  Map.lookup (n, normalizedArgs) specializationMap <&> \monoName ->
                    phantom (TypeCon monoName)
            Nothing -> Nothing
          applyRewrites :: IsTerm a => Annotated TypeCheck a -> Annotated TypeCheck a
          applyRewrites = sub (embedSub rewriteTy)

      -- Build the specialized DeclTypeData
      let (_ :< DeclTypeData _ _ _ specCons) = applyRewrites specData
          monoCons = zipWith
            (\((srcCon, _) :< DataCon _ argTy) monoConName ->
              let monoConQTy = phantom (Mono (phantom (TypeFn argTy (phantom (TypeCon monoDataName)))))
              in  (srcCon, monoConQTy) :< DataCon monoConName argTy)
            specCons monoConNames
          monoDecl :: Annotated TypeCheck DeclType
          monoDecl = phantom (DeclTypeData mode monoDataName [] monoCons)

      -- Cast to Monomorphize stage and emit
      monoDecl' <- castTerm monoDecl
      monomorphizeState . outputDecls %= (++ [phantom (DeclType monoDecl')])

      return monoDataName

monomorphizePat :: Annotated TypeCheck Pat -> Praxis (Annotated Monomorphize Pat)
monomorphizePat ((src, ty) :< pat) = case pat of
  PatData conName innerPat -> do
    monoConName <- monoConNameFor conName ty
    innerPat'   <- monomorphizePat innerPat
    return ((src, ty) :< PatData monoConName innerPat')
  _ -> ((src, ty) :<) <$> recurseTerm castTerm pat
  where
    monoConNameFor conName ty = do
      dataName <- (monomorphizeState . conToDataType) `uses` Map.lookup conName
      case dataName of
        Nothing -> return conName  -- non-polymorphic, keep as-is
        Just dn -> do
          Just (_ :< DeclTypeData _ _ typePats _) <-
            (monomorphizeState . polyDataDecls) `uses` Map.lookup dn
          case unapplyTypeCon (stripViews ty) of
            Just (_, concreteArgs) -> do
              let subst = zip typePats concreteArgs
              _  <- specializeDataType dn subst
              let monoTypes = map snd (normalizeSubst subst)
              monoName <- (monomorphizeState . specializations) `uses` Map.lookup (conName, monoTypes)
              return (fromJust monoName)
            Nothing -> return conName

monomorphizeProgram :: Annotated TypeCheck Program -> Praxis ()
monomorphizeProgram (_ :< Program decls) = do
  mapM_ collect decls
  mapM_ emit decls
  where
    -- First pass: populate polyDecls with polymorphic definitions
    collect :: Annotated TypeCheck Decl -> Praxis ()
    collect (_ :< decl) = case decl of
      DeclTerm dt -> collectDeclTerm dt
      DeclRec ds  -> mapM_ collectDeclRec ds
      DeclType dt -> collectDeclType dt
      _           -> return ()

    collectDeclRec :: Annotated TypeCheck DeclRec -> Praxis ()
    collectDeclRec (_ :< DeclRecTerm dt) = collectDeclTerm dt
    collectDeclRec (_ :< DeclRecType dt) = collectDeclType dt

    collectDeclType :: Annotated TypeCheck DeclType -> Praxis ()
    collectDeclType dt = case view value dt of
      DeclTypeData _ name typePats cons | not (null typePats) -> do
        monomorphizeState . polyDataDecls %= Map.insert name dt
        forM_ cons $ \(_ :< DataCon conName _) ->
          monomorphizeState . conToDataType %= Map.insert conName name
      _ -> return ()

    collectDeclTerm :: Annotated TypeCheck DeclTerm -> Praxis ()
    collectDeclTerm dt = case view value dt of
      DeclTermVar name (Just qt) _
        | (_ :< Poly _ _ _) <- qt -> monomorphizeState . polyDecls %= Map.insert name dt
      _ -> return ()

    -- Second pass: emit non-polymorphic declarations
    emit :: Annotated TypeCheck Decl -> Praxis ()
    emit ann = case view value ann of
      DeclTerm dt | isPolymorphic dt -> return ()
      DeclRec ds  | any (isPolyRec . view value) ds -> return ()
      DeclType dt | isPolymorphicDT dt -> return ()
      _ -> do
        monoDecl <- castTerm ann
        monomorphizeState . outputDecls %= (++ [monoDecl])


    isPolymorphicDT :: Annotated TypeCheck DeclType -> Bool
    isPolymorphicDT (_ :< DeclTypeData _ _ typePats _) = not (null typePats)
    isPolymorphicDT _                                  = False

    isPolyRec :: DeclRec TypeCheck -> Bool
    isPolyRec (DeclRecTerm dt) = isPolymorphic dt
    isPolyRec (DeclRecType dt) = isPolymorphicDT dt
