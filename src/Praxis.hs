{-# LANGUAGE GADTs             #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes        #-}
{-# LANGUAGE TemplateHaskell   #-}

module Praxis
  ( Praxis
  , PraxisState

  -- | State types
  , CEnv(..)
  , InstanceOrigin(..)
  , Instance(..)
  , IEnv(..)
  , KEnv(..)
  , TEnv(..)
  , VEnv(..)

  -- | Operators
  , Fixity(..)
  , OpDefns
  , OpContext(..)
  , defns
  , levels
  , prec

  , warn
  , warnAt
  , throw
  , throwAt
  , abort

  , save
  , try

  , runPraxis

  -- | Lift an IO computation to the Praxis monad
  , liftIO
  , liftIOUnsafe

  -- | Flag lenses
  , debug
  , silent

  -- | Praxis lenses
  , flags
  , fresh
  , stage
  , opContext
  , cEnv
  , iEnv
  , kEnv
  , tEnv
  , vEnv
  , typeSynonyms
  , typeCheckState
  , kindCheckState

  , freshKindUni
  , freshRef
  , freshTypeUni
  , freshVar

  , clearTerm
  , ifFlag
  , display

  , requireMain
  )
  where

import qualified Check.State                  as Check
import           Common
import           Print
import           Stage
import           Term
import           Value

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
import qualified Data.Monoid.Colorful         as Colored
import qualified Env.Lazy
import qualified Env.Linear
import qualified Env.Strict
import           Introspect
import qualified System.Console.Terminal.Size as Terminal


data Flags = Flags
  { _debug  :: Bool
  , _silent :: Bool -- silence IO (for tests, and for internal runs which are guaranteed not to throw / use IO)
  } deriving (Show)

data Fresh = Fresh
  { _freshKindUnis      :: [String]
  , _freshRefs          :: [String]
  , _freshTypeUniPlains :: [String]
  , _freshTypeUniRefs   :: [String]
  , _freshTypeUniValues :: [String]
  , _freshTypeUniViews  :: [String]
  , _freshVars          :: Map Name Int
  }

type CEnv = Env.Strict.Env (Annotated QType)

data InstanceOrigin = Inbuilt | Trivial | User
  deriving Eq

data Instance = IsInstance | IsInstanceOnlyIf [TypeConstraint]

type IEnv = Env.Strict.Env (Map Name ([Annotated Type] -> (InstanceOrigin, Instance)))

type KEnv = Env.Strict.Env (Annotated Kind)

type TEnv = Env.Linear.Env (Annotated QType)

type VEnv = Env.Lazy.Env Value

data Fixity = Infix (Maybe Assoc)
            | Prefix
            | Postfix
            | Closed
  deriving (Eq, Ord)

type OpDefns = Map Op (Name, Fixity)

data OpContext = OpContext { _defns :: OpDefns, _levels :: [[Op]], _prec :: Graph }

makeLenses ''OpContext

data PraxisState = PraxisState
  { _flags          :: Flags               -- ^ Flags
  , _fresh          :: Fresh
  , _stage          :: Stage               -- ^ Current stage of compilation
  , _opContext      :: OpContext
  , _cEnv           :: CEnv                -- ^ Constructor environment
  , _iEnv           :: IEnv                -- ^ Instance environment
  , _kEnv           :: KEnv                -- ^ Kind environment
  , _tEnv           :: TEnv                -- ^ Type environment
  , _vEnv           :: VEnv                -- ^ Value environment
  , _typeSynonyms   :: Map Name (Annotated Type) -- ^ Type synonyms
  , _typeCheckState :: Check.State TypeConstraint
  , _kindCheckState :: Check.State KindConstraint
  }

type Praxis = ExceptT String (StateT PraxisState IO)

defaultFlags :: Flags
defaultFlags = Flags { _debug = False, _silent = False }

defaultFresh = Fresh
  { _freshKindUnis    = map (("^k"++) . show) [0..]
  , _freshRefs        = map (("'l"++) . show) [0..]
  , _freshTypeUniPlains = map (("^t"++) . show) [0..]
  , _freshTypeUniRefs   = map (("^r"++) . show) [0..]
  , _freshTypeUniValues = map (("^s"++) . show) [0..]
  , _freshTypeUniViews  = map (("^v"++) . show) [0..]
  , _freshVars        = Map.empty
  }

emptyState :: PraxisState
emptyState = PraxisState
  { _flags          = defaultFlags
  , _fresh          = defaultFresh
  , _stage          = Unknown
  , _opContext      = OpContext { _defns = Map.empty, _prec = array (0, -1) [], _levels = [] }
  , _cEnv           = Env.Strict.empty
  , _iEnv           = Env.Strict.empty
  , _kEnv           = Env.Strict.empty
  , _tEnv           = Env.Linear.empty
  , _vEnv           = Env.Lazy.empty
  , _typeSynonyms   = Map.empty
  , _typeCheckState = Check.emptyState
  , _kindCheckState = Check.emptyState
  }

makeLenses ''Flags
makeLenses ''Fresh
makeLenses ''PraxisState

format :: Pretty a => a -> Praxis (Colored String)
format x = do
  stage' <- use stage
  let opt = case stage' of { KindCheck -> Kinds; TypeCheck -> Types; _ -> Simple }
  return (runPrintable (pretty x) opt)

abort :: Pretty a => a -> Praxis b
abort x = do
  displayBare x
  err <- fold <$> format x
  ExceptT (return (Left err))

withContext :: Printable String -> Maybe Source -> Praxis (Printable String)
withContext message src = do
  stage' <- use stage
  let
    stageStr = case stage' of
      Unknown -> blank
      _       -> pretty (Colored.Value (show stage')) <> " "
    srcStr = case src of
      Nothing  -> blank
      Just src -> " at " <> pretty (Colored.Style Bold (Colored.Value (show src)))
  return $ stageStr <> message <> srcStr

warn' :: Pretty a => Maybe Source -> a -> Praxis ()
warn' src x = (`ifFlag` debug) $ do
  message <- pretty (Colored.Style Bold (Colored.Fg Yellow ("warning" :: Colored String))) `withContext` src
  displayBare (message <> ": " <> pretty x)

warn :: Pretty a => a -> Praxis ()
warn = warn' Nothing

warnAt :: Pretty a => Source -> a -> Praxis ()
warnAt src = warn' (Just src)

throw' :: Pretty a => Maybe Source -> a -> Praxis b
throw' src x = do
  message <- pretty (Colored.Style Bold (Colored.Fg Red ("error" :: Colored String))) `withContext` src
  abort $ message <> ": " <> pretty x

throw :: Pretty a => a -> Praxis b
throw = throw' Nothing

throwAt :: Pretty a => Source -> a -> Praxis b
throwAt src = throw' (Just src)

display :: Pretty a => String -> a -> Praxis ()
display info x = unlessSilent $ do
  t <- liftIO $ getTerm
  s <- use stage
  liftIO $ printColoredS t $ Colored.Fg White (Colored.Bg Green (Colored.Style Bold (Colored.Value (show s ++ " (" ++ info ++ ")")))) <> "\n"
  displayBare x

displayBare :: Pretty a => a -> Praxis ()
displayBare x = unlessSilent $ do
  t <- liftIO $ getTerm
  x <- format x
  liftIO $ printColoredS t $ x <> "\n"

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
  (x, t) <- liftIO $ runPraxis' p s
  case x of
    Left e  -> lift (State.put s) >> return Nothing
    Right y -> lift (State.put t) >> return (Just y)

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

runPraxis' :: Praxis a -> PraxisState -> IO (Either String a, PraxisState)
runPraxis' = runStateT . runExceptT

runPraxis :: Praxis a -> IO (Either String a)
runPraxis c = fst <$> runPraxis' c emptyState

ifFlag :: Praxis () -> Lens' Flags Bool -> Praxis ()
ifFlag c f = use (flags . f) >>= (flip when) c

freshKindUni :: Praxis (Annotated Kind)
freshKindUni = do
  (k:ks) <- use (fresh . freshKindUnis)
  fresh . freshKindUnis .= ks
  return (phantom (KindUni k))

freshRef :: Praxis (Annotated Type)
freshRef = do
  (l:ls) <- use (fresh . freshRefs)
  fresh . freshRefs .= ls
  return (TypeRef l `as` phantom KindType)

freshTypeUni :: Flavor -> Praxis (Annotated Type)
freshTypeUni f = case f of
  Plain -> freshTypeUni' freshTypeUniPlains KindType
  Ref   -> freshTypeUni' freshTypeUniRefs KindRef
  Value -> freshTypeUni' freshTypeUniValues KindType
  View  -> freshTypeUni' freshTypeUniViews KindView
  where
    freshTypeUni' :: Lens' Fresh [String] -> Kind -> Praxis (Annotated Type)
    freshTypeUni' freshTypeUnis kind = do
      (x:xs) <- use (fresh . freshTypeUnis)
      fresh . freshTypeUnis .= xs
      return (TypeUni f x `as` phantom kind)

freshVar :: Name -> Praxis Name
freshVar var = do
  m <- use (fresh . freshVars)
  let i = Map.findWithDefault 0 var m
  fresh . freshVars .= (Map.insert var (i+1) m)
  return ("_" ++ var ++ "_" ++ show i)

requireMain :: Praxis ()
requireMain = do
  ty <- tEnv `uses` Env.Linear.lookup "main_0"
  case ty of
    Nothing -> throw ("missing main function" :: String)
    Just ty
      | (_ :< Mono (_ :< TypeFn (_ :< TypeUnit) (_ :< TypeUnit))) <- ty
        -> return ()
      | otherwise
        -> throwAt (view source ty) $ "main function has bad type " <> pretty ty <> ", expected () -> ()"
