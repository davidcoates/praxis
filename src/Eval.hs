{-# LANGUAGE NamedFieldPuns    #-}
{-# LANGUAGE OverloadedStrings #-}

module Eval
  ( run
  ) where

import           Common
import qualified Env.Strict        as Env
import           Praxis
import           Stage
import           Term
import qualified Value
import           Value             (Value, integerToValue, valueToInteger)

import           Control.Monad.Fix (mfix)
import           Data.Array.IO
import           Data.List         (partition)
import           Data.Maybe        (mapMaybe)


run :: Annotated Snippet -> Praxis Value
run snippet = save stage $ do
  stage .= Evaluate
  clearTerm `ifFlag` debug
  evalSnippet snippet

evalSnippet :: Annotated Snippet -> Praxis Value
evalSnippet (_ :< Snippet decls exp) = do
  traverse evalDecl decls
  evalExp exp

evalDecl :: Annotated Decl -> Praxis ()
evalDecl (_ :< decl) = case decl of

  DeclTerm (_ :< decl) -> case decl of

    DeclTermFn name captures (arg, argTy) exp -> do
      let
        fn = Value.Fn $ \val -> save fEnv $ do
          fEnv %= Env.insert arg val
          evalExp exp
      vEnv %= Env.insert name fn

    DeclTermVar name _ exp -> do
      value <- evalExp exp
      vEnv %= Env.insert name value

  DeclType _    -> return ()


getValue :: Source -> Name -> Praxis Value
getValue src name = do
  entry1 <- vEnv `uses` Env.lookup name
  entry2 <- fEnv `uses` Env.lookup name
  case (entry1, entry2) of
     (Just val, Nothing) -> return val
     (Nothing, Just val) -> return val
     (Nothing, Nothing)  -> throwAt src ("unknown variable " <> pretty name)
     (Just _, Just _)    -> throwAt src ("duplicated variable " <> pretty name)

evalExp :: Annotated Exp -> Praxis Value
evalExp ((src, Just t) :< exp) = case exp of

  Apply f x -> do
    Value.Fn f <- evalExp f
    x <- evalExp x
    f x

  Closure name captures -> do
    let names = map fst captures
    values <- mapM (getValue src) names
    fn <- getValue src name
    let
      wrap :: Value -> Value
      wrap (Value.Polymorphic polyFun) = Value.Polymorphic (\sp -> wrap (polyFun sp))
      wrap (Value.Fn fn) = Value.Fn $ \val -> save fEnv $ do
        fEnv .= Env.fromList (zip names values)
        fn val
    return (wrap fn)

  Case exp alts -> do
    val <- evalExp exp
    evalCase src val alts

  Con name -> do
    case t of
      (_ :< TypeFn _ _) -> return $ Value.Fn (\val -> return $ Value.Data name val)
      _                 -> return $ Value.Enum name

  Defer exp1 exp2 -> do
    val <- evalExp exp1
    evalExp exp2
    return val

  If condExp thenExp elseExp -> do
    Value.Bool cond <- evalExp condExp
    if cond then evalExp thenExp else evalExp elseExp

  Let bind exp -> save fEnv $ do
    evalBind bind
    evalExp exp

  Lit lit -> pure $ case lit of
    Bool    val -> Value.Bool val
    Char    val -> Value.Char val
    Integer val -> let (_ :< TypeCon n) = t in integerToValue n val
    String  val -> Value.String val

  Read _ exp -> evalExp exp

  Pair exp1 exp2 -> Value.Pair <$> evalExp exp1 <*> evalExp exp2

  Seq exp1 exp2 -> do
    evalExp exp1
    val <- evalExp exp2
    return val

  Sig exp _ -> evalExp exp

  Specialise exp specialisation -> do
    exp <- evalExp exp
    case exp of
      Value.Polymorphic polyFun -> return (polyFun specialisation)
      _                         -> return exp

  Switch alts -> evalSwitch src alts

  Term.Unit -> return Value.Unit

  Var var -> do
    display "var" var
    getValue src var


evalSwitch :: Source -> [(Annotated Exp, Annotated Exp)] -> Praxis Value
evalSwitch src [] = throwAt src ("inexhaustive switch" :: String)
evalSwitch src ((condExp,bodyExp):alts) = do
  cond <- evalExp condExp
  case cond of
    Value.Bool True  -> evalExp bodyExp
    Value.Bool False -> evalSwitch src alts

evalCase :: Source -> Value -> [(Annotated Pat, Annotated Exp)] -> Praxis Value
evalCase src val [] = throwAt src ("no matching pattern for value " <> pretty (show val))
evalCase src val ((pat,exp):alts) = case tryMatch val pat of
  Just doMatch -> save fEnv $ do
    doMatch
    evalExp exp
  Nothing ->
    evalCase src val alts

forceMatch :: Source -> Value -> Annotated Pat -> Praxis ()
forceMatch src val pat = case tryMatch val pat of
  Just doMatch -> doMatch
  Nothing -> throwAt src ("no matching pattern for value " <> pretty (show val))

evalBind :: Annotated Bind -> Praxis ()
evalBind ((src, _) :< Bind pat exp) = do
  exp <- evalExp exp
  forceMatch src exp pat

tryMatch :: Value -> Annotated Pat -> Maybe (Praxis ())
tryMatch val ((_, Just t) :< pat) = case pat of

  PatAt name pat
    -> (\doMatch -> do { fEnv %= Env.insert name val; doMatch }) <$> tryMatch val pat

  PatData name pat | Value.Data name' val <- val
    -> if name == name' then tryMatch val pat else Nothing

  PatEnum name | Value.Enum name' <- val
    -> if name == name' then Just (return ()) else Nothing

  PatHole
    -> Just (return ())

  PatLit pat -> if match then Just (return ()) else Nothing where
    match = case (pat, val) of
      (Bool v, Value.Bool v') -> v == v'
      (Char v, Value.Char v') -> v == v'
      (Integer v, v')         -> v == valueToInteger v'
      _                       -> False

  PatPair pat1 pat2 | Value.Pair val1 val2 <- val
    -> liftA2 (>>) (tryMatch val1 pat1) (tryMatch val2 pat2)

  PatUnit
    -> Just (return ())

  PatVar name
    -> Just $ fEnv %= Env.insert name val

  _
    -> Nothing
