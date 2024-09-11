{-# LANGUAGE GADTs             #-}
{-# LANGUAGE OverloadedStrings #-}

module Check.Type.Rename
  ( run
  , intro
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
  display "renamed term" term `ifFlag` debug
  return term

rename :: Term a => Annotated a -> Praxis (Annotated a)
rename term = ($ term) $ case typeof (view value term) of
  IBind     -> renameBind
  IDeclTerm -> renameDeclTerm
  IExp      -> renameExp
  IPat      -> renamePat
  _         -> value (recurseTerm rename)


disambiguate :: Source -> Name -> Praxis Name
disambiguate src var = Check.disambiguate typeCheckState src (Plain, var)

intro :: Name -> Praxis Name
intro var = Check.intro typeCheckState (Plain, var)

introMany :: Source -> [Name] -> Praxis [Name]
introMany src vars = Check.introMany typeCheckState src (map (\var -> (Plain, var)) vars)

introFromPat :: Annotated Pat -> Praxis ()
introFromPat pat = do
  let vars = extract (embedMonoid f) pat
      f = \case
        PatVar n  -> [n]
        PatAt n _ -> [n]
        _         -> []
  introMany (view source pat) vars
  return ()

renameDeclTerm :: Annotated DeclTerm -> Praxis (Annotated DeclTerm)
renameDeclTerm (a@(src, _) :< decl) = (a :<) <$> case decl of

  DeclTermVar name sig exp -> do
    exp <- renameExp exp
    name <- intro name
    return $ DeclTermVar name sig exp

  DeclTermRec decls -> do
    let names = map (\(_ :< DeclTermVar name _ _) -> name) decls
    names <- introMany src names
    decls <- traverse (\(name, decl) -> value (renameDeclTermVar name) decl) (zip names decls)
    return (DeclTermRec decls)

  where
    renameDeclTermVar :: Name -> DeclTerm -> Praxis DeclTerm
    renameDeclTermVar name (DeclTermVar _ sig exp) = DeclTermVar name sig <$> renameExp exp


renameAlt :: (Annotated Pat, Annotated Exp) -> Praxis (Annotated Pat, Annotated Exp)
renameAlt (pat, exp) = save (typeCheckState . scopes) $ do
  introFromPat pat
  pat <- renamePat pat
  exp <- renameExp exp
  return (pat, exp)

renameBind :: Annotated Bind -> Praxis (Annotated Bind)
renameBind (a :< Bind pat exp) = do
  exp <- renameExp exp
  introFromPat pat
  pat <- renamePat pat
  return (a :< Bind pat exp)

renameExp :: Annotated Exp -> Praxis (Annotated Exp)
renameExp (a@(src, _) :< exp) = (a :<) <$> case exp of

  Var name -> Var <$> disambiguate src name

  Read name exp -> Read <$> disambiguate src name <*> renameExp exp

  Where exp decls -> save (typeCheckState . scopes) $ do
    decls <- traverse renameDeclTerm decls
    exp <- renameExp exp
    return $ Where exp decls

  Case exp alts -> do
    exp <- renameExp exp
    alts <- traverse renameAlt alts
    return $ Case exp alts

  Cases alts -> do
    alts <- traverse renameAlt alts
    return $ Cases alts

  Lambda pat _ -> save (typeCheckState . scopes) $ do
    introFromPat pat
    recurseTerm rename exp

  Let bind exp -> save (typeCheckState . scopes) $ do
    bind <- renameBind bind
    exp <- renameExp exp
    return $ Let bind exp

  _ -> recurseTerm rename exp


renamePat :: Annotated Pat -> Praxis (Annotated Pat)
renamePat (a@(src, _) :< pat) = (a :<) <$> case pat of

  PatVar n  -> PatVar <$> disambiguate src n

  PatAt n p -> PatAt <$> disambiguate src n <*> renamePat p

  _         -> recurseTerm rename pat
