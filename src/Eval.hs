{-# LANGUAGE NamedFieldPuns    #-}
{-# LANGUAGE OverloadedStrings #-}

module Eval
  ( runExp
  , runProgram
  ) where

import           Common
import qualified Env.Lazy          as Env
import           Praxis
import           Stage
import           Term
import qualified Value
import           Value             (Value, integerToValue, valueToInteger)

import           Control.Monad.Fix (mfix)
import           Data.Array.IO
import           Data.List         (partition)
import           Data.Maybe        (mapMaybe)

runExp :: Annotated Exp -> Praxis Value
runExp exp = save stage $ do
  stage .= Evaluate
  clearTerm `ifFlag` debug
  evalExp exp

runProgram :: Annotated Program -> Praxis ()
runProgram program = save stage $ do
  stage .= Evaluate
  clearTerm `ifFlag` debug
  evalProgram program

evalProgram :: Annotated Program -> Praxis ()
evalProgram (_ :< Program decls) = do
  traverse evalDecl decls
  return ()

-- | A helper for decls, irrefutably matching the [b] argument
irrefMapM :: Monad m => ((a, b) -> m c) -> [a] -> [b] -> m [c]
irrefMapM f as bs = case as of
  []     -> return []
  (a:as) -> case bs of
    ~(b:bs) -> do
      c <- f (a, b)
      cs <- irrefMapM f as bs
      return (c : cs)

evalDecl :: Annotated Decl -> Praxis ()
evalDecl (_ :< decl) = case decl of

  DeclTerm decl -> evalDeclTerm decl

  DeclType _    -> return ()


evalDeclTerm :: Annotated DeclTerm -> Praxis ()
evalDeclTerm (_ :< decl) = case decl of

  DeclTermRec decls -> do
    let (names, exps) = unzip [ (name, exp) | (_ :< DeclTermVar name _ exp) <- decls ]
    -- To support mutual recursion, each function needs to see the evaluation of all other functions (including itself).
    -- Leverage mfix to find the fixpoint.
    mfix $ \values -> do
      -- Evaluate each of the functions in turn, with all of the evaluations in the environment
      -- Note: The use of irrefMapM here is essential to avoid divergence of mfix.
      irrefMapM (\(name, value) -> vEnv %= Env.insert name value) names values
      mapM evalExp exps
    return ()

  DeclTermVar name _ exp -> do
    value <- evalExp exp
    vEnv %= Env.insert name value


getValue :: Source -> Name -> Praxis Value
getValue src name = do
  entry <- vEnv `uses` Env.lookup name
  case entry of
     Just val -> return val
     Nothing  -> throwAt src ("unknown variable: " <> quote (pretty name))

evalExp :: Annotated Exp -> Praxis Value
evalExp ((src, Just t) :< exp) = case exp of

  Apply f x -> do
    Value.Fn f <- evalExp f
    x <- evalExp x
    f x

  Case exp alts -> do
    val <- evalExp exp
    evalCase src val alts

  Cases alts -> return $ Value.Fn $ \val -> evalCase src val alts

  Closure captures exp -> do
    let names = map fst captures
    values <- mapM (getValue src) names
    Value.Fn fn <- evalExp exp
    return $ Value.Fn $ \val -> save vEnv $ do
      vEnv .= Env.fromList (zip names values)
      fn val

  Con name -> do
    case t of
      (_ :< TypeFn _ _) -> return $ Value.Fn (\val -> return $ Value.Data name val)
      _                -> return $ Value.Enum name

  Defer exp1 exp2 -> do
    val <- evalExp exp1
    evalExp exp2
    return val

  If condExp thenExp elseExp -> do
    Value.Bool cond <- evalExp condExp
    if cond then evalExp thenExp else evalExp elseExp

  Lambda pat exp -> return $ Value.Fn $ \val -> forceMatch src val pat >> evalExp exp

  Let bind exp -> save vEnv $ do
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

  Var var -> getValue src var

  Where exp decls -> save vEnv $ do
    traverse evalDeclTerm decls
    evalExp exp


evalSwitch :: Source -> [(Annotated Exp, Annotated Exp)] -> Praxis Value
evalSwitch src [] = throwAt src ("inexhaustive switch" :: String)
evalSwitch src ((condExp,bodyExp):alts) = do
  cond <- evalExp condExp
  case cond of
    Value.Bool True  -> evalExp bodyExp
    Value.Bool False -> evalSwitch src alts

evalCase :: Source -> Value -> [(Annotated Pat, Annotated Exp)] -> Praxis Value
evalCase src val [] = throwAt src ("no matching pattern for value " <> quote (pretty (show val)))
evalCase src val ((pat,exp):alts) = case tryMatch val pat of
  Just doMatch -> save vEnv $ do
    doMatch
    evalExp exp
  Nothing ->
    evalCase src val alts

forceMatch :: Source -> Value -> Annotated Pat -> Praxis ()
forceMatch src val pat = case tryMatch val pat of
  Just doMatch -> doMatch
  Nothing -> throwAt src ("no matching pattern for value " <> quote (pretty (show val)))

evalBind :: Annotated Bind -> Praxis ()
evalBind ((src, _) :< Bind pat exp) = do
  exp <- evalExp exp
  forceMatch src exp pat

tryMatch :: Value -> Annotated Pat -> Maybe (Praxis ())
tryMatch val ((_, Just t) :< pat) = case pat of

  PatAt name pat
    -> (\doMatch -> do { vEnv %= Env.insert name val; doMatch }) <$> tryMatch val pat

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
    -> Just $ vEnv %= Env.insert name val

  _
    -> Nothing
