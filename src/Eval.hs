{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE NamedFieldPuns         #-}
{-# LANGUAGE OverloadedStrings      #-}

module Eval
  ( Evaluable(..)
  ) where

import           Check.Type.Generate (recursive)
import           Common
import           Env
import           Praxis
import           Stage
import           Term
import           Value               (Value)
import qualified Value

import           Control.Monad.Fix   (mfix)
import           Data.Array.IO
import           Data.List           (partition)
import           Data.Maybe          (mapMaybe)
import           Prelude             hiding (exp, lookup)

class Evaluable a b | a -> b where
  eval' :: Annotated a -> Praxis b
  eval  :: Annotated a -> Praxis b
  eval term = save stage $ do
    stage .= Evaluate
    clearTerm `ifFlag` debug
    eval' term

instance Evaluable Program () where
  eval' = evalProgram

instance Evaluable Exp Value where
  eval' = evalExp

evalProgram :: Annotated Program -> Praxis ()
evalProgram (_ :< Program decls) = evalDecls decls

-- | A helper for decls, irrefutably matching the [b] argument
irrefMapM :: Monad m => ((a, b) -> m c) -> [a] -> [b] -> m [c]
irrefMapM f as bs = case as of
  []     -> return []
  (a:as) -> case bs of
    ~(b:bs) -> do
      c <- f (a, b)
      cs <- irrefMapM f as bs
      return (c : cs)


evalDecls :: [Annotated Decl] -> Praxis ()
evalDecls decls = do

  -- Only variable declartions (values / functions) can be evaluated, so we only need to consider DeclVar
  let declVar :: Annotated Decl -> Maybe (Name, Annotated Exp)
      declVar = \case
        (_ :< DeclVar var _ exp) -> Just (var, exp)
        _ -> Nothing
      (vars, exps) = unzip (mapMaybe declVar decls)

  -- To support mutual recursion, each value needs to see the evaluation of all other values (including itself).
  -- Leverage mfix to find the fixpoint (where vs stands for the list of evaluations).
  mfix $ \values -> do
    -- Evaluate each of the values in turn, with all of the evaluations in the environment
    -- Note: The use of irrefMapM here is essential to avoid divergence of mfix.
    irrefMapM (\(var, value) -> vEnv %= intro var value) vars values
    mapM evalExp exps

  return ()


evalStmt :: Annotated Stmt -> Praxis ()
evalStmt (_ :< stmt) = case stmt of

  StmtBind bind -> evalBind bind

  StmtExp exp   -> evalExp exp >> return ()


evalExp :: Annotated Exp -> Praxis Value
evalExp ((src, _) :< exp) = case exp of

  Apply f x -> do
    Value.Fun f <- evalExp f
    x <- evalExp x
    f x

  Case exp alts -> do
    val <- evalExp exp
    evalCases src val alts

  Cases alts -> do
    l <- use vEnv
    return $ Value.Fun $ \val -> save vEnv $ do { vEnv .= l; evalCases src val alts }

  Con name -> do
    Just dataAlt <- daEnv `uses` lookup name
    let DataConInfo { argType } = view (annotation . just) dataAlt
    return $ case argType of
      Nothing -> Value.Con name Nothing
      Just _  -> Value.Fun (\val -> return $ Value.Con name (Just val))

  Do stmts -> save vEnv $ do
    mapM evalStmt (init stmts)
    let _ :< StmtExp lastExp = last stmts
    evalExp lastExp

  If condExp thenExp elseExp -> do
    Value.Bool cond <- evalExp condExp
    if cond then evalExp thenExp else evalExp elseExp

  Lambda pat exp -> do
    l <- use vEnv
    return $ Value.Fun $ \val -> save vEnv $ do { vEnv .= l; forceBind src val pat; evalExp exp }

  Let bind exp -> save vEnv $ do
    evalBind bind
    evalExp exp

  Lit lit -> case lit of
    Bool val   -> pure $ Value.Bool val
    Char val   -> pure $ Value.Char val
    Int val    -> pure $ Value.Int  val
    String val -> Value.Array <$> Value.fromString val

  Read _ exp -> evalExp exp

  Pair exp1 exp2 -> Value.Pair <$> evalExp exp1 <*> evalExp exp2

  Sig exp _ -> evalExp exp

  Switch alts -> evalSwitch src alts

  Term.Unit -> return Value.Unit

  Var var -> do
    entry <- vEnv `uses` lookup var
    case entry of
       Just val -> return val
       Nothing  -> throwAt src ("unknown variable " <> quote (pretty var))

  Where exp decls -> save vEnv $ do
    evalDecls decls
    evalExp exp


evalSwitch :: Source -> [(Annotated Exp, Annotated Exp)] -> Praxis Value
evalSwitch src [] = throwAt src ("inexhaustive switch" :: String)
evalSwitch src ((condExp,bodyExp):alts) = do
  cond <- evalExp condExp
  case cond of
    Value.Bool True  -> evalExp bodyExp
    Value.Bool False -> evalSwitch src alts

evalCases :: Source -> Value -> [(Annotated Pat, Annotated Exp)] -> Praxis Value
evalCases src val [] = throwAt src ("no matching pattern for value " <> quote (pretty (show val)))
evalCases src val ((pat,exp):alts) = case tryBind val pat of
  Just doBind -> save vEnv $ do
    doBind
    evalExp exp
  Nothing ->
    evalCases src val alts

forceBind :: Source -> Value -> Annotated Pat -> Praxis ()
forceBind src val pat = case tryBind val pat of
  Just doBind -> doBind
  Nothing -> throwAt src ("no matching pattern for value " <> quote (pretty (show val)))

evalBind :: Annotated Bind -> Praxis ()
evalBind ((src, _) :< Bind pat exp) = do
  exp <- evalExp exp
  forceBind src exp pat

tryBind :: Value -> Annotated Pat -> Maybe (Praxis ())
tryBind val (_ :< pat) = case pat of

  PatAt name pat
    -> (\doBind -> do { vEnv %= intro name val; doBind }) <$> tryBind val pat

  PatCon patCon pat | Value.Con valCon val <- val
    -> if patCon /= valCon then Nothing else case (pat, val) of
      (Nothing, Nothing)   -> Just (return ())
      (Just pat, Just val) -> tryBind val pat

  PatHole
    -> Just (return ())

  PatLit pat -> if match then Just (return ()) else Nothing where
    match = case (pat, val) of
      (Bool v, Value.Bool v') -> v == v'
      (Char v, Value.Char v') -> v == v'
      (Int v,  Value.Int  v') -> v == v'
      _                       -> False

  PatPair pat1 pat2 | Value.Pair val1 val2 <- val
    -> liftA2 (>>) (tryBind val1 pat1) (tryBind val2 pat2)

  PatUnit
    -> Just (return ())

  PatVar name
    -> Just $ vEnv %= intro name val
  _
    -> Nothing
