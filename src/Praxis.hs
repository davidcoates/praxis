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

  -- |Operators
  , Fixity(..)
  , OpDefns
  , OpContext(..)
  , defns
  , levels
  , prec

  , throw
  , throwAt
  , abort

  , save
  , try

  , runPraxis
  , runInternal

  -- |Lift an IO computation to the Praxis monad
  , liftIOUnsafe
  , liftIO

  -- |Flag lenses
  , debug
  , interactive

  -- |Praxis lenses
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
  , tSynonyms
  , system

  , freshTyUni
  , freshKindUni
  , freshTyOpUni
  , freshVar
  , freshTyVar
  , freshTyOpVar
  , reuse

  , clearTerm
  , ifFlag
  , display
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
import qualified Data.Map.Strict              as Map (empty)
import           Data.Maybe                   (fromMaybe)
import qualified Data.Set                     as Set
import qualified Env                          as Env (Environment (..))
import           Env.Env
import           Env.LEnv
import qualified System.Console.Terminal.Size as Terminal
import           System.IO.Unsafe             (unsafePerformIO)
import           Value

data Flags = Flags
  { _debug       :: Bool
  , _interactive :: Bool
  , _static      :: Bool              -- ^Set for internal pure computations evaluated at compile time
  } deriving (Show)

data Fresh = Fresh
  { _freshTyUnis   :: [String]
  , _freshTyOpUnis :: [String]
  , _freshKindUnis :: [String]
  , _freshVars     :: [String]
  , _freshTyVars   :: [String]
  , _freshTyOpVars :: [String]
  }

instance Show Fresh where
  show _ = "<fresh>"

type VEnv = Env Name Value

type TEnv = LEnv Name (Annotated QType)

type KEnv = Env Name (Annotated Kind)

type DAEnv = Env Name (Annotated DataAlt)

data Fixity = Infix (Maybe Assoc)
            | Prefix
            | Postfix
            | Closed
  deriving (Eq, Ord)

type OpDefns = Map Op (Name, Fixity)

data OpContext = OpContext { _defns :: OpDefns, _levels :: [[Op]], _prec :: Graph }

makeLenses ''OpContext

data PraxisState = PraxisState
  { _infile    :: Maybe String
  , _outfile   :: Maybe String
  , _flags     :: Flags               -- ^Flags
  , _fresh     :: Fresh
  , _stage     :: Stage               -- ^Current stage of compilation
  , _opContext :: OpContext
  , _kEnv      :: KEnv                -- ^Kind environment
  , _tEnv      :: TEnv                -- ^Type environment
  , _daEnv     :: DAEnv               -- ^Data alternative environment
  , _vEnv      :: VEnv                -- ^Value environment for interpreter
  , _tSynonyms :: Map Name (Annotated Type) -- ^Type synonyms TODO encapsulate within desugarer?
  , _system    :: Check.System        -- ^ TODO rename?
  }

instance Show PraxisState where
  show s = "<praxis state>"

type Praxis = MaybeT (StateT PraxisState IO)

newtype PraxisT f a = PraxisT { runPraxisT :: f (Praxis a) }

instance MonadTrans PraxisT where
  lift x = PraxisT (pure <$> x)

instance Functor f => Functor (PraxisT f) where
  fmap f (PraxisT x) = PraxisT (fmap (fmap f) x)

defaultFlags :: Flags
defaultFlags = Flags { _debug = False, _interactive = False, _static = False }

defaultFresh = Fresh
  { _freshTyUnis   = map (("?t"++) . show) [0..]
  , _freshTyOpUnis = map (("?o"++) . show) [0..]
  , _freshKindUnis = map (("?k"++) . show) [0..]
  , _freshVars     = map (("?v"++) . show) [0..]
  , _freshTyVars   = map (("'t"++) . show) [0..]
  , _freshTyOpVars = map (("'o"++) . show) [0..]
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
  , _tSynonyms    = Map.empty
  , _system       = error ("unset system") -- FIXME Checkers are responsible for initialisating system
  }

makeLenses ''Flags
makeLenses ''Fresh
makeLenses ''PraxisState

throw :: Pretty a => a -> Praxis b
throw x = displayBare (pretty (Style Bold (Fg DullRed ("error: " :: Colored String))) <> pretty x) >> empty

throwAt :: Pretty a => Source -> a -> Praxis b
throwAt s x = displayBare (pretty (Style Bold (Value (show s)) <> " " <> Style Bold (Fg DullRed ("error: " :: Colored String))) <> pretty x) >> empty

abort :: Pretty a => a -> Praxis b
abort x = displayBare x >> empty

display :: Pretty a => a -> Praxis ()
display x = do
  t <- liftIO $ getTerm
  s <- use stage
  liftIO $ printColoredS t $ "\n{- " <> Style Italic (Value (show s)) <> " -}\n\n"
  displayBare x

displayBare :: Pretty a => a -> Praxis ()
displayBare x = do
  t <- liftIO $ getTerm
  s <- use stage
  let o = case s of { KindCheck _ -> Kinds; TypeCheck _ -> Types; _ -> Plain }
  liftIO $ printColoredS t $ runPrintable (pretty x) o <> "\n"

clearTerm :: Praxis ()
clearTerm = liftIO $ do
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
    Nothing -> lift (State.put s) >> return Nothing
    Just y  -> lift (State.put t) >> return (Just y)

runInternal :: PraxisState -> Praxis a -> a
runInternal s c = case fst $ unsafePerformIO (runPraxis c' s) of
  Nothing -> error "static computation failed"
  Just x  -> x
  where c' = (flags . static .= True) >> c

liftIOUnsafe :: IO a -> Praxis a
liftIOUnsafe io = lift (lift io)

liftIO :: IO a -> Praxis a
liftIO io = do
  s <- use (flags . static)
  if s then empty else liftIOUnsafe io

runPraxis :: Praxis a -> PraxisState -> IO (Maybe a, PraxisState)
runPraxis = runStateT . runMaybeT

ifFlag :: Praxis () -> Lens' Flags Bool -> Praxis ()
ifFlag c f = use (flags . f) >>= (flip when) c

freshTyUni :: Praxis (Annotated Type)
freshTyUni = do
  (x:xs) <- use (fresh . freshTyUnis)
  fresh . freshTyUnis .= xs
  return (TyUni x `as` phantom KindType)

freshTyOpUni :: Praxis (Annotated TyOp)
freshTyOpUni = do
  (o:os) <- use (fresh . freshTyOpUnis)
  fresh . freshTyOpUnis .= os
  return (phantom (TyOpUni o))

freshKindUni :: Praxis (Annotated Kind)
freshKindUni = do
  (k:ks) <- use (fresh . freshKindUnis)
  fresh . freshKindUnis .= ks
  return (phantom (KindUni k))

freshVar :: Praxis Name
freshVar = do
  (x:xs) <- use (fresh . freshVars)
  fresh . freshVars .= xs
  return x

freshTyVar :: Praxis (Annotated Type)
freshTyVar = do
  (x:xs) <- use (fresh . freshTyVars)
  fresh . freshTyVars .= xs
  return (TyVar x `as` phantom KindType)

freshTyOpVar :: Praxis (Annotated TyOp)
freshTyOpVar = do
  (o:os) <- use (fresh . freshTyOpVars)
  fresh . freshTyOpVars .= os
  return (phantom (TyOpVar o))

-- This will fuck things up if the name is still used somewhere
reuse :: Name -> Praxis ()
reuse _ = pure ()
{-
reuse n@('?':c:_) = over (fresh . f c) (n:)
  where f 'a' = freshTyUnis
        f 'e' = freshTyOpUnis
        f 'k' = freshKindUnis
-}
