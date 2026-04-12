{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE UndecidableInstances #-}

module Lower.Monomorphize
  ( run
  , Monomorphization(..)
  ) where

import           Common
import           Introspect
import           Lower.State
import           Praxis
import           Stage
import           Term

import           Data.Map.Strict     (Map)
import qualified Data.Map.Strict     as Map
import           Data.Maybe          (fromJust)
import           Data.Set            (Set)
import qualified Data.Set            as Set

import           Control.Lens        (makeLenses)
import           Control.Monad       (forM, forM_)
import           Control.Monad.State (StateT, runStateT)
import           Control.Monad.Trans (lift)
import           Data.List           (partition)


data MonoLocal = MonoLocal
  { _topLevelDecls  :: [Annotated Lower Decl]
  -- ^ Monomorphic declarations emitted at the top level.
  , _localPolyNames :: Set Name
  -- ^ Names of polymorphic functions declared in the current Where scope.
  , _pendingDecls   :: [Annotated Lower DeclTerm]
  -- ^ Monomorphic declarations pending injection into the current Where body.
  }

makeLenses ''MonoLocal

emptyMonoLocal :: MonoLocal
emptyMonoLocal = MonoLocal
  { _topLevelDecls  = []
  , _localPolyNames = Set.empty
  , _pendingDecls   = []
  }

type MonoM = StateT MonoLocal Praxis

type family Monomorphization a where
  Monomorphization Program = Annotated Lower Program
  Monomorphization Exp     = (Annotated Lower Program, Annotated Lower Exp)

run :: IsTerm a => Annotated TypeCheck a -> Praxis (Monomorphization a)
run term = case typeof (view value term) of

  ProgramT -> do
    ((), local) <- runStateT (monomorphizeProgram term) emptyMonoLocal
    let program = phantom (Program (view topLevelDecls local))
    display Lower "monomorphized program" program `ifFlag` debug
    return program

  ExpT -> do
    (exp, local) <- runStateT (monomorphizeExp term) emptyMonoLocal
    let program = phantom (Program (view topLevelDecls local))
    display Lower "monomorphized program" program `ifFlag` debug
    display Lower "monomorphized exp" exp `ifFlag` debug
    return (program, exp)

  _ -> error "Lower.Monomorphize.run: unexpected term type"

-- | Apply a substitution over any term.
-- Replaces each TypeVar whose name appears in the substitution with the corresponding concrete type.
applySubst :: IsTerm a => Substitution TypeCheck -> Annotated TypeCheck a -> Annotated TypeCheck a
applySubst subst = sub (embedSub f)
  where
    mapping = [ (n, ty) | (_ :< TypePatVar _ n, ty) <- subst ]
    f :: Annotated TypeCheck Type -> Maybe (Annotated TypeCheck Type)
    f (_ :< TypeVar _ n) = lookup n mapping
    f _                  = Nothing

-- | Cross-stage traversal from TypeCheck to Lower.
-- Must enumerate each case so GHC can reduce the Annotation type family.
monomorphize :: forall a. IsTerm a => Annotated TypeCheck a -> MonoM (Annotated Lower a)
monomorphize term = ($ term) $ case typeof (view value term) of
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
    auto :: (IsTerm a, Annotation TypeCheck a ~ Annotation Lower a) => Annotated TypeCheck a -> MonoM (Annotated Lower a)
    auto = value (recurseTerm monomorphize)

monomorphizeExp :: Annotated TypeCheck Exp -> MonoM (Annotated Lower Exp)
monomorphizeExp ((src, ty) :< exp) = case exp of

  Specialize inner subst -> case view value inner of

    Var name -> do
      monoName <- specialize name subst
      return ((src, ty) :< Var monoName)

    Con name -> do
      Just dataName <- lift $ (lowerState . conToDataType) `uses` Map.lookup name
      _ <- specializeDataType dataName subst
      let monoTypes = map snd (normalizeSubst subst)
      Just monoConName <- lift $ (lowerState . specializations) `uses` Map.lookup (name, monoTypes)
      return ((src, ty) :< Con monoConName)

    Inbuilt _ -> ((src, ty) :<) <$> recurseTerm monomorphize exp

  Where body decls -> do
    let (wherePolyDecls, whereMonoDecls) = partition isPolymorphic decls
        newLocalPolyNames = Set.fromList [ name | (_ :< DeclTermVar name _ _) <- wherePolyDecls ]
    saveLift (lowerState . polyDecls) $ save localPolyNames $ save pendingDecls $ do
      forM_ wherePolyDecls $ \dt -> case view value dt of
        DeclTermVar name _ _ -> lift $ lowerState . polyDecls %= Map.insert name dt
        _                    -> return ()
      localPolyNames %= Set.union newLocalPolyNames
      pendingDecls .= []
      whereMonoDecls' <- traverse monomorphize whereMonoDecls
      monoBody <- monomorphizeExp body
      innerPending <- use pendingDecls
      return ((src, ty) :< Where monoBody (innerPending ++ whereMonoDecls'))

  _ -> ((src, ty) :<) <$> recurseTerm monomorphize exp


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
specialize :: Name -> Substitution TypeCheck -> MonoM Name
specialize name subst = do
  let subst' = normalizeSubst subst
      types  = map snd subst'
  existing <- lift $ (lowerState . specializations) `uses` Map.lookup (name, types)
  case existing of
    Just monoName -> return monoName
    Nothing -> do
      monoName <- lift $ freshVar name
      -- Register before processing body to handle recursive self-calls
      lift $ lowerState . specializations %= Map.insert (name, types) monoName
      Just polyDecl <- lift $ (lowerState . polyDecls) `uses` Map.lookup name
      localNames <- use localPolyNames
      let isLocal = Set.member name localNames
      monoDecl <- specializeDeclTerm monoName subst' polyDecl
      if isLocal
        then do
          let (_ :< DeclTerm dt) = monoDecl
          pendingDecls %= (++ [dt])
        else
          topLevelDecls %= (++ [monoDecl])
      return monoName

-- | Produce a monomorphic DeclTermVar by substituting the specialization into a polymorphic definition.
specializeDeclTerm :: Name -> Substitution TypeCheck -> Annotated TypeCheck DeclTerm -> MonoM (Annotated Lower Decl)
specializeDeclTerm monoName subst (_ :< DeclTermVar _ qTy bodyExp) = do
  let monoTy = fmap (\qt -> case view value qt of
        Poly _ _ ty -> phantom (Mono (applySubst subst ty))
        Mono ty     -> phantom (Mono ty)) qTy
  monoBody <- monomorphizeExp (applySubst subst bodyExp)
  monoQTy  <- traverse monomorphize monoTy
  return (phantom (DeclTerm (phantom (DeclTermVar monoName monoQTy monoBody))))

-- | Look up or create the monomorphic name for a specialization of a polymorphic data type.
specializeDataType :: Name -> Substitution TypeCheck -> MonoM Name
specializeDataType dataName subst = do
  let subst' = normalizeSubst subst
      types  = map snd subst'
  existing <- lift $ (lowerState . specializations) `uses` Map.lookup (dataName, types)
  case existing of
    Just monoDataName -> return monoDataName
    Nothing -> do
      Just polyDecl <- lift $ (lowerState . polyDataDecls) `uses` Map.lookup dataName
      let (_ :< DeclTypeData mode _ typePats cons) = polyDecl

      -- Register mono data type name FIRST (before processing body, handles recursion)
      monoDataName <- lift $ freshVar dataName
      lift $ lowerState . specializations %= Map.insert (dataName, types) monoDataName

      -- Register a mono name for each constructor
      monoConNames <- forM cons $ \(_ :< DataCon conName _) -> do
        monoConName <- lift $ freshVar conName
        lift $ lowerState . specializations %= Map.insert (conName, types) monoConName
        return monoConName

      -- Apply type-variable substitution to the whole DeclTypeData body
      let specData = applySubst subst' polyDecl

      -- Build a type-rewriting function: TypeApply (TypeCon n) args -> TypeCon monoN
      -- Snapshot taken here, after registering all mono names for this data type and its
      -- constructors, but before processing nested specializations. This is intentional:
      -- rewriteTy only needs to resolve type constructors referenced in the body of this
      -- data type, which must already be registered (either pre-existing or just added above).
      specializationMap <- lift $ use (lowerState . specializations)
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

      -- Cast to Lower stage and emit
      monoDecl' <- monomorphize monoDecl
      topLevelDecls %= (++ [phantom (DeclType monoDecl')])

      return monoDataName


monomorphizePat :: Annotated TypeCheck Pat -> MonoM (Annotated Lower Pat)
monomorphizePat ((src, ty) :< pat) = case pat of
  PatData conName innerPat -> do
    monoConName <- monoConNameFor conName ty
    innerPat'   <- monomorphizePat innerPat
    return ((src, ty) :< PatData monoConName innerPat')
  _ -> ((src, ty) :<) <$> recurseTerm monomorphize pat
  where
    monoConNameFor conName ty = do
      dataName <- lift $ (lowerState . conToDataType) `uses` Map.lookup conName
      case dataName of
        Nothing -> return conName  -- non-polymorphic, keep as-is
        Just dn -> do
          Just (_ :< DeclTypeData _ _ typePats _) <-
            lift $ (lowerState . polyDataDecls) `uses` Map.lookup dn
          case unapplyTypeCon (stripViews ty) of
            Just (_, concreteArgs) -> do
              let subst = zip typePats concreteArgs
              _  <- specializeDataType dn subst
              let monoTypes = map snd (normalizeSubst subst)
              monoName <- lift $ (lowerState . specializations) `uses` Map.lookup (conName, monoTypes)
              return (fromJust monoName)
            Nothing -> return conName

monomorphizeProgram :: Annotated TypeCheck Program -> MonoM ()
monomorphizeProgram (_ :< Program decls) = do
  lift $ mapM_ collect decls
  mapM_ emitDecl decls
  where
    -- First pass: populate polyDecls/polyDataDecls (pure Praxis state, no output)
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
        lowerState . polyDataDecls %= Map.insert name dt
        forM_ cons $ \(_ :< DataCon conName _) ->
          lowerState . conToDataType %= Map.insert conName name
      _ -> return ()

    collectDeclTerm :: Annotated TypeCheck DeclTerm -> Praxis ()
    collectDeclTerm dt = case view value dt of
      DeclTermVar name (Just qt) _
        | (_ :< Poly _ _ _) <- qt -> lowerState . polyDecls %= Map.insert name dt
      _ -> return ()

    -- Second pass: emit non-polymorphic declarations
    emitDecl :: Annotated TypeCheck Decl -> MonoM ()
    emitDecl ann = case view value ann of
      DeclTerm dt | isPolymorphic dt -> return ()
      DeclRec ds  | any (isPolyRec . view value) ds -> return ()
      DeclType dt | isPolymorphicDT dt -> return ()
      _ -> do
        monoDecl <- monomorphize ann
        topLevelDecls %= (++ [monoDecl])

    isPolymorphicDT :: Annotated TypeCheck DeclType -> Bool
    isPolymorphicDT (_ :< DeclTypeData _ _ typePats _) = not (null typePats)
    isPolymorphicDT _                                  = False

    isPolyRec :: DeclRec TypeCheck -> Bool
    isPolyRec (DeclRecTerm dt) = isPolymorphic dt
    isPolyRec (DeclRecType dt) = isPolymorphicDT dt
