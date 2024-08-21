{-# LANGUAGE GADTs             #-}
{-# LANGUAGE OverloadedStrings #-}

module Check.Kind.Rename
  ( run
  ) where


import qualified Check.Rename as Check
import           Check.State
import           Common
import           Introspect
import           Praxis
import           Print
import           Term


run :: Term a => Annotated a -> Praxis (Annotated a)
run term = do
  term <- rename term
  display term `ifFlag` debug
  return term

rename :: Term a => Annotated a -> Praxis (Annotated a)
rename term = ($ term) $ case typeof (view value term) of
  IDeclTerm -> renameDeclTerm
  IDeclType -> renameDeclType
  IType     -> renameType
  ITyPat    -> renameTyPat
  IQType    -> renameQType
  IQTyVar   -> renameQTyVar
  IView     -> renameView
  _         -> value (recurseTerm rename)


disambiguate :: Source -> Name -> Praxis Name
disambiguate = Check.disambiguate kindCheckState

intro :: Name -> Praxis Name
intro = Check.intro kindCheckState

introMany :: Source -> [Name] -> Praxis [Name]
introMany = Check.introMany kindCheckState

introFromTyPats :: Source -> [Annotated TyPat] -> Praxis ()
introFromTyPats src tyPats = do
  let tyVar (_ :< tyPat) = case tyPat of
        TyPatVar n       -> n
        TyPatViewVar _ n -> n
      tyVars = map tyVar tyPats
  introMany src tyVars
  return ()

introFromQType :: Annotated QType -> Praxis ()
introFromQType ((src, _) :< qTy) = case qTy of
  Forall vs _ _ -> do
    let tyVars = [ n | QTyVar n <- map (view value) vs ] ++ [ n | QViewVar _ n <- map (view value) vs ]
    introMany src tyVars
    return ()
  Mono _ -> return ()

renameDeclTerm :: Annotated DeclTerm -> Praxis (Annotated DeclTerm)
renameDeclTerm (a@(src, _) :< decl) = (a :<) <$> case decl of

  DeclTermVar name sig exp -> do
    case sig of
      Nothing  -> recurseTerm rename decl
      Just sig -> save (kindCheckState . scopes) $ introFromQType sig >> (DeclTermVar name <$> (Just <$> recurse rename sig) <*> recurse rename exp)

  _ -> recurseTerm rename decl


renameDeclType :: Annotated DeclType -> Praxis (Annotated DeclType)
renameDeclType (a@(src, _) :< decl) = (a :< ) <$> case decl of

  DeclTypeData _ _ tyPats _ -> save (kindCheckState . scopes) $ introFromTyPats src tyPats >> recurseTerm rename decl

  _ -> recurseTerm rename decl


renameType :: Annotated Type -> Praxis (Annotated Type)
renameType (a@(src, _) :< ty) = (a :<) <$> case ty of

  TyVar n -> TyVar <$> disambiguate src n

  _       -> recurseTerm rename ty


renameTyPat :: Annotated TyPat -> Praxis (Annotated TyPat)
renameTyPat (a@(src, _) :< tyPat) = (a :<) <$> case tyPat of

  TyPatVar n       -> TyPatVar <$> disambiguate src n

  TyPatViewVar d n -> TyPatViewVar d <$> disambiguate src n


renameView  :: Annotated View -> Praxis (Annotated View)
renameView (a@(src, _) :< v) = (a :<) <$> case v of

  ViewVar d n -> ViewVar d <$> disambiguate src n

  _           -> recurseTerm rename v


renameQType :: Annotated QType -> Praxis (Annotated QType)
renameQType qTy = save (kindCheckState . scopes) $ introFromQType qTy >> recurse rename qTy

renameQTyVar :: Annotated QTyVar -> Praxis (Annotated QTyVar)
renameQTyVar (a@(src, _) :< qTyVar) = (a :<) <$> case qTyVar of

  QTyVar n     -> QTyVar <$> disambiguate src n

  QViewVar d n -> QViewVar d <$> disambiguate src n
