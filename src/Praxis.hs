{-# LANGUAGE GADTs             #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes        #-}
{-# LANGUAGE TemplateHaskell   #-}

module Praxis
  ( Praxis
  , PraxisState
  , emptyState

  -- | State types
  , CEnv(..)
  , Instance(..)
  , IEnv(..)
  , KEnv(..)
  , TEnv(..)
  , System(..)

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
  , runDebug
  , runSilent
  , runInternal

  -- | Lift an IO computation to the Praxis monad
  , liftIO
  , liftIOUnsafe

  -- | Flag lenses
  , debug

  -- | System lenses
  , requirements
  , assumptions

  -- | Praxis lenses
  , flags
  , fresh
  , stage
  , opContext
  , cEnv
  , iEnv
  , kEnv
  , tEnv
  , rewriteMap
  , tySynonyms
  , tySystem
  , kindSystem

  -- | RewriteMap lenses
  , tyVarMap
  , varMap

  , freshTyUni
  , freshKindUni
  , freshTyViewUni
  , freshViewRef
  , freshTyVar
  , freshVar

  , clearTerm
  , ifFlag
  , display

  , requireMain
  )
  where

import           Common
import           Print
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
import           Data.Set                     (Set)
import qualified Data.Set                     as Set
import           Env.Env                      (Env)
import qualified Env.Env                      as Env
import           Env.LEnv                     (LEnv)
import qualified Env.LEnv                     as LEnv
import           Introspect
import qualified System.Console.Terminal.Size as Terminal
import           System.IO.Unsafe             (unsafePerformIO)

data Flags = Flags
  { _debug  :: Bool
  , _silent :: Bool -- silence IO (for tests, and for internal runs which are guaranteed not to throw / use IO)
  } deriving (Show)

data Fresh = Fresh
  { _freshTyUnis   :: [String]
  , _freshViewUnis :: [String]
  , _freshKindUnis :: [String]
  , _freshViewRefs :: [String]
  , _freshTyVars   :: Map Name Int
  , _freshVars     :: Map Name Int
  }

type CEnv = Env (Annotated QType)

data Instance = IsInstance | IsInstanceOnlyIf [Annotated Type]

type IEnv = Env (Map Name (Maybe (Annotated Type) -> Instance))

type KEnv = Env (Annotated Kind)

type TEnv = LEnv (Annotated QType)

data Fixity = Infix (Maybe Assoc)
            | Prefix
            | Postfix
            | Closed
  deriving (Eq, Ord)

type OpDefns = Map Op (Name, Fixity)

data OpContext = OpContext { _defns :: OpDefns, _levels :: [[Op]], _prec :: Graph }

makeLenses ''OpContext

data RewriteMap = RewriteMap { _tyVarMap :: Map Name Name, _varMap :: Map Name Name }

makeLenses ''RewriteMap

data System c = System
  { _requirements :: [Annotated (Requirement c)] -- TODO colored string?
  , _assumptions  :: Set c
  }

emptySystem :: System c
emptySystem = System
  { _requirements = []
  , _assumptions  = Set.empty
  }

makeLenses ''System

data PraxisState = PraxisState
  { _flags      :: Flags               -- ^ Flags
  , _fresh      :: Fresh
  , _stage      :: Stage               -- ^ Current stage of compilation
  , _opContext  :: OpContext
  , _cEnv       :: CEnv                -- ^ Constructor environment
  , _iEnv       :: IEnv                -- ^ Instance environment
  , _kEnv       :: KEnv                -- ^ Kind environment
  , _tEnv       :: TEnv                -- ^ Type environment
  -- TODO encapsulate within desugarer?
  , _tySynonyms :: Map Name (Annotated Type) -- ^ Type synonyms
  , _rewriteMap :: RewriteMap
  , _tySystem   :: System TyConstraint
  , _kindSystem :: System KindConstraint
  }

type Praxis = ExceptT String (StateT PraxisState IO)

defaultFlags :: Flags
defaultFlags = Flags { _debug = False, _silent = False }

defaultFresh = Fresh
  { _freshTyUnis   = map (("^t"++) . show) [0..]
  , _freshViewUnis = map (("^v"++) . show) [0..]
  , _freshKindUnis = map (("^k"++) . show) [0..]
  , _freshViewRefs = map (("'l"++) . show) [0..]
  , _freshTyVars   = Map.empty
  , _freshVars     = Map.empty
  }

emptyState :: PraxisState
emptyState = PraxisState
  { _flags        = defaultFlags
  , _fresh        = defaultFresh
  , _stage        = Unknown
  , _opContext    = OpContext { _defns = Map.empty, _prec = array (0, -1) [], _levels = [] }
  , _cEnv         = Env.empty
  , _iEnv         = Env.empty
  , _kEnv         = Env.empty
  , _tEnv         = LEnv.empty
  , _tySynonyms   = Map.empty
  , _rewriteMap   = RewriteMap { _tyVarMap = Map.empty, _varMap = Map.empty }
  , _tySystem     = emptySystem
  , _kindSystem   = emptySystem
  }

makeLenses ''Flags
makeLenses ''Fresh
makeLenses ''PraxisState

format :: Pretty a => a -> Praxis (Colored String)
format x = do
  stage' <- use stage
  let opt = case stage' of { KindCheck -> Kinds; TypeCheck -> Types; _ -> Plain }
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
      _       -> pretty (Value (show stage')) <> " "
    srcStr = case src of
      Nothing  -> blank
      Just src -> " at " <> pretty (Style Bold (Value (show src)))
  return $ stageStr <> message <> srcStr

warnAt :: Pretty a => Source -> a -> Praxis ()
warnAt src x = (`ifFlag` debug) $ do
  message <- pretty (Style Bold (Fg DullYellow ("warning" :: Colored String))) `withContext` (Just src)
  displayBare (message <> ": " <> pretty x)

throw' :: Pretty a => Maybe Source -> a -> Praxis b
throw' src x = do
  message <- pretty (Style Bold (Fg DullRed ("error" :: Colored String))) `withContext` src
  abort $ message <> ": " <> pretty x

throw :: Pretty a => a -> Praxis b
throw x = throw' Nothing x

throwAt :: Pretty a => Source -> a -> Praxis b
throwAt src x = throw' (Just src) x

display :: Pretty a => a -> Praxis ()
display x = unlessSilent $ do
  t <- liftIO $ getTerm
  s <- use stage
  liftIO $ printColoredS t $ "\n{- " <> Style Italic (Value (show s)) <> " -}\n\n"
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
  (x, t) <- liftIO $ runPraxis p s
  case x of
    Left e  -> lift (State.put s) >> return Nothing
    Right y -> lift (State.put t) >> return (Just y)

runDebug :: PraxisState -> Praxis a -> IO (Either String a)
runDebug s c = do
  (x, _) <- runPraxis (flags . debug .= True >> c) s
  return x

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

freshTyViewUni :: ViewDomain -> Praxis (Annotated Type)
freshTyViewUni domain = do
  (o:os) <- use (fresh . freshViewUnis)
  fresh . freshViewUnis .= os
  return (TyView (ViewUni domain o `as` phantom (KindView domain)) `as` phantom (KindView domain))

freshKindUni :: Praxis (Annotated Kind)
freshKindUni = do
  (k:ks) <- use (fresh . freshKindUnis)
  fresh . freshKindUnis .= ks
  return (phantom (KindUni k))

freshViewRef :: Praxis (Annotated View)
freshViewRef = do
  (l:ls) <- use (fresh . freshViewRefs)
  fresh . freshViewRefs .= ls
  return (ViewRef l `as` phantom (KindView Ref))

freshTyVar :: Name -> Praxis Name
freshTyVar var = do
  m <- use (fresh . freshTyVars)
  let i = Map.findWithDefault 0 var m
  fresh . freshTyVars .= (Map.insert var (i+1) m)
  return (var ++ "_" ++ show i)

freshVar :: Name -> Praxis Name
freshVar var = do
  m <- use (fresh . freshVars)
  let i = Map.findWithDefault 0 var m
  fresh . freshVars .= (Map.insert var (i+1) m)
  return (var ++ "_" ++ show i)

requireMain :: Praxis ()
requireMain = do
  ty <- tEnv `uses` LEnv.lookup "main_0"
  case ty of
    Nothing -> throw ("missing main function" :: String)
    Just ty
      | (_ :< Forall [] [] (_ :< TyApply (_ :< TyCon "Fn") (_ :< TyPack (_ :< TyCon "Unit") (_ :< TyCon "Unit")))) <- ty
        -> return ()
      | otherwise
        -> throwAt (view source ty) $ "main function has bad type " <> quote (pretty ty) <> ", expected () -> ()"
