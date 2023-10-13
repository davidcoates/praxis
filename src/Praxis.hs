{-# LANGUAGE GADTs             #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes        #-}
{-# LANGUAGE TemplateHaskell   #-}

module Praxis
  ( Praxis
  , PraxisT(..)
  , PraxisState
  , emptyState

  , KEnv(..)
  , TEnv(..)
  , DAEnv(..)
  , VEnv(..)

  -- | Operators
  , Fixity(..)
  , OpDefns
  , OpContext(..)
  , defns
  , levels
  , prec

  , warnAt
  , throw
  , throwAt
  , abort

  , save
  , try

  , runPraxis
  , runSilent
  , runInternal

  -- | Lift an IO computation to the Praxis monad
  , liftIO
  , liftIOUnsafe

  -- | Flag lenses
  , debug
  , interactive

  -- | Praxis lenses
  , infile
  , outfile
  , flags
  , fresh
  , stage
  , opContext
  , kEnv
  , tEnv
  , daEnv
  , vEnv
  , tyVarMap
  , tySynonyms
  , system

  , freshTyUni
  , freshKindUni
  , freshTyOpUni
  , freshTyVar
  , freshTyOpVar
  , freshTyOpRef
  , reuse

  , clearTerm
  , ifFlag
  , display
  , sanitise
  )
  where

import qualified Check.System                 as Check (System)
import           Common
import           Stage
import           Term

import           Control.Applicative          (empty, liftA2)
import           Control.Concurrent
import           Control.Lens                 (Lens', makeLenses, traverseOf)
import           Control.Monad.Trans.Class    (MonadTrans (..))
import qualified Control.Monad.Trans.State    as State (get, modify, put)
import           Data.Array                   (array)
import           Data.Graph                   (Graph)
import           Data.Map.Strict              (Map)
import qualified Data.Map.Strict              as Map
import           Data.Maybe                   (fromMaybe)
import qualified Data.Set                     as Set
import qualified Env                          as Env (Environment (..))
import           Env.Env
import           Env.LEnv
import           Env.SEnv
import           Introspect
import qualified System.Console.Terminal.Size as Terminal
import           System.IO.Unsafe             (unsafePerformIO)
import           Value

data Flags = Flags
  { _debug       :: Bool
  , _interactive :: Bool
  , _silent      :: Bool -- silence IO (for tests, and for internal runs which are guaranteed not to throw / use IO)
  } deriving (Show)

data Fresh = Fresh
  { _freshTyUnis   :: [String]
  , _freshTyOpUnis :: [String]
  , _freshKindUnis :: [String]
  , _freshTyVars   :: [String]
  , _freshTyOpVars :: [String]
  , _freshTyOpRefs :: [String]
  }

instance Show Fresh where
  show _ = "<fresh>"

type VEnv = Env Name Value

type TEnv = LEnv Name (Annotated QType)

type KEnv = Env Name (Annotated Kind)

type DAEnv = Env Name (Annotated DataCon)

data Fixity = Infix (Maybe Assoc)
            | Prefix
            | Postfix
            | Closed
  deriving (Eq, Ord)

type OpDefns = Map Op (Name, Fixity)

data OpContext = OpContext { _defns :: OpDefns, _levels :: [[Op]], _prec :: Graph }

makeLenses ''OpContext

data PraxisState = PraxisState
  { _infile     :: Maybe String
  , _outfile    :: Maybe String
  , _flags      :: Flags               -- ^ Flags
  , _fresh      :: Fresh
  , _stage      :: Stage               -- ^ Current stage of compilation
  , _opContext  :: OpContext
  , _kEnv       :: KEnv                -- ^ Kind environment
  , _tEnv       :: TEnv                -- ^ Type environment
  , _daEnv      :: DAEnv               -- ^ Data alternative environment
  , _vEnv       :: VEnv                -- ^ Value environment for interpreter
  -- TODO encapsulate within desugarer?
  , _tySynonyms :: Map Name (Annotated Type) -- ^ Type synonyms
  , _tyVarMap   :: Map Name Name       -- ^ Substitutions to apply to TyVar / TyVarOp when printing
  -- TODO rename?
  , _system     :: Check.System        -- ^ Type/Kind check state
  }

instance Show PraxisState where
  show s = "<praxis state>"

type Praxis = ExceptT String (StateT PraxisState IO)

newtype PraxisT f a = PraxisT { runPraxisT :: f (Praxis a) }

instance MonadTrans PraxisT where
  lift x = PraxisT (pure <$> x)

instance Functor f => Functor (PraxisT f) where
  fmap f (PraxisT x) = PraxisT (fmap (fmap f) x)

defaultFlags :: Flags
defaultFlags = Flags { _debug = False, _interactive = False, _silent = False }

defaultFresh = Fresh
  { _freshTyUnis   = map (("^t"++) . show) [0..]
  , _freshTyOpUnis = map (("^o"++) . show) [0..]
  , _freshKindUnis = map (("^k"++) . show) [0..]
  , _freshTyVars   = map (("'t"++) . show) [0..]
  , _freshTyOpVars = map (("'o"++) . show) [0..]
  , _freshTyOpRefs = map (("'l"++) . show) [0..]
  }

emptyState :: PraxisState
emptyState = PraxisState
  { _infile       = Nothing
  , _outfile      = Nothing
  , _flags        = defaultFlags
  , _fresh        = defaultFresh
  , _stage        = Unknown
  , _opContext    = OpContext { _defns = Map.empty, _prec = array (0, -1) [], _levels = [] }
  , _kEnv         = Env.empty
  , _tEnv         = Env.empty
  , _daEnv        = Env.empty
  , _vEnv         = Env.empty
  , _tySynonyms   = Map.empty
  , _tyVarMap     = Map.empty
  , _system       = error ("unset system") -- FIXME Checkers are responsible for initialisating system
  }

makeLenses ''Flags
makeLenses ''Fresh
makeLenses ''PraxisState

abort :: Pretty a => a -> Praxis b
abort x = displayBare x >> ExceptT (return (Left err)) where
  err = fold (runPrintable (pretty x) Plain)

warnAt :: Pretty a => Source -> a -> Praxis ()
warnAt s x = displayBare (pretty (Style Bold (Value (show s)) <> " " <> Style Bold (Fg DullYellow ("warning: " :: Colored String))) <> pretty x) `ifFlag` debug

throw :: Pretty a => a -> Praxis b
throw x = abort (pretty (Style Bold (Fg DullRed ("error: " :: Colored String))) <> pretty x)

throwAt :: Pretty a => Source -> a -> Praxis b
throwAt s x = abort (pretty (Style Bold (Value (show s)) <> " " <> Style Bold (Fg DullRed ("error: " :: Colored String))) <> pretty x)

display :: Pretty a => a -> Praxis ()
display x = unlessSilent $ do
  t <- liftIO $ getTerm
  s <- use stage
  liftIO $ printColoredS t $ "\n{- " <> Style Italic (Value (show s)) <> " -}\n\n"
  displayBare x

displayBare :: Pretty a => a -> Praxis ()
displayBare x = unlessSilent $ do
  t <- liftIO $ getTerm
  s <- use stage
  let o = case s of { KindCheck _ -> Kinds; TypeCheck _ -> Types; _ -> Plain }
  liftIO $ printColoredS t $ runPrintable (pretty x) o <> "\n"

clearTerm :: Praxis ()
clearTerm = unlessSilent $ liftIO $ do
  putStrLn ""
  Terminal.size >>= \case
    Just (Terminal.Window _ w) -> putStrLn $ replicate w '='
    Nothing                    -> pure ()

save :: Lens' PraxisState a -> Praxis b -> Praxis b
save l c = do
  x <- use l
  r <- c
  l .= x
  return r

try :: Praxis a -> Praxis (Maybe a)
try p = do
  s <- lift State.get
  (x, t) <- liftIO $ runPraxis p s
  case x of
    Left e  -> lift (State.put s) >> return Nothing
    Right y -> lift (State.put t) >> return (Just y)

runSilent :: PraxisState -> Praxis a -> IO (Either String a)
runSilent s c = do
  (x, _) <- runPraxis (flags . silent .= True >> c) s
  return x

runInternal :: PraxisState -> Praxis a -> a
runInternal s c = case unsafePerformIO (runSilent s c) of
  Left e  -> error ("internal computation failed: " ++ e)
  Right x -> x

unlessSilent :: Praxis () -> Praxis ()
unlessSilent c = do
  s <- use (flags . silent)
  if s then pure () else c

liftIO :: IO a -> Praxis a
liftIO io = do
  s <- use (flags . silent)
  if s then error "attempted IO in silent mode" else lift (lift io)

liftIOUnsafe :: IO a -> Praxis a
liftIOUnsafe io = lift (lift io)

runPraxis :: Praxis a -> PraxisState -> IO (Either String a, PraxisState)
runPraxis = runStateT . runExceptT

ifFlag :: Praxis () -> Lens' Flags Bool -> Praxis ()
ifFlag c f = use (flags . f) >>= (flip when) c

freshTyUni :: Praxis (Annotated Type)
freshTyUni = do
  (x:xs) <- use (fresh . freshTyUnis)
  fresh . freshTyUnis .= xs
  return (TyUni x `as` phantom KindType)

freshTyOpUni :: TyOpDomain -> Praxis (Annotated TyOp)
freshTyOpUni domain = do
  (o:os) <- use (fresh . freshTyOpUnis)
  fresh . freshTyOpUnis .= os
  return (phantom (TyOpUni domain o))

freshKindUni :: Praxis (Annotated Kind)
freshKindUni = do
  (k:ks) <- use (fresh . freshKindUnis)
  fresh . freshKindUnis .= ks
  return (phantom (KindUni k))

freshTyVar :: Praxis (Annotated Type)
freshTyVar = do
  (x:xs) <- use (fresh . freshTyVars)
  fresh . freshTyVars .= xs
  return (TyVar x `as` phantom KindType)

freshTyOpVar :: TyOpDomain -> Praxis (Annotated TyOp)
freshTyOpVar domain = do
  (o:os) <- use (fresh . freshTyOpVars)
  fresh . freshTyOpVars .= os
  return (phantom (TyOpVar domain o))

freshTyOpRef :: Praxis (Annotated TyOp)
freshTyOpRef = do
  (l:ls) <- use (fresh . freshTyOpRefs)
  fresh . freshTyOpRefs .= ls
  return (phantom (TyOpRef l))

-- This will fuck things up if the name is still used somewhere
reuse :: Name -> Praxis ()
reuse _ = pure ()
{-
reuse n@('?':c:_) = over (fresh . f c) (n:)
  where f 'a' = freshTyUnis
        f 'e' = freshTyOpUnis
        f 'k' = freshKindUnis
-}

-- | Unrewrite type (operator) variables
sanitise :: Term a => Annotated a -> Praxis (Annotated a)
sanitise x = do
  m <- use tyVarMap
  let rewriteTyVars :: Term a => Annotated a -> Annotated a
      rewriteTyVars = sub $ \x -> case typeof x of
        IType   |        TyVar n <- x ->        TyVar <$> n `Map.lookup` m
        ITyOp   |    TyOpVar d n <- x ->    TyOpVar d <$> n `Map.lookup` m
        ITyPat  |     TyPatVar n <- x ->     TyPatVar <$> n `Map.lookup` m
        ITyPat  | TyPatOpVar d n <- x -> TyPatOpVar d <$> n `Map.lookup` m
        IQTyVar |       QTyVar n <- x ->       QTyVar <$> n `Map.lookup` m
        IQTyVar |   QTyOpVar d n <- x ->   QTyOpVar d <$> n `Map.lookup` m
        _                             -> Nothing
  return (rewriteTyVars x)
