{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs            #-}
{-# LANGUAGE Rank2Types       #-}

module Inbuilts
  ( initialState
  ) where

import           Common
import           Env.KEnv     (KEnv)
import qualified Env.KEnv     as KEnv (fromList)
import           Env.TEnv     (TEnv)
import qualified Env.TEnv     as TEnv (fromList)
import           Env.VEnv     (VEnv)
import qualified Env.VEnv     as VEnv (fromList)
import           Introspect
import           Parse        (parse)
import           Praxis
import qualified Record
import           Term
import           Value

import           Control.Lens as Lens (set)
import           Data.List    (nub, sort)
import qualified Data.Set     as Set (empty)

-- TODO Make this importPrelude, a Monadic action?
initialState :: PraxisState
initialState = set tEnv initialTEnv $ set vEnv initialVEnv $ set kEnv initialKEnv $ emptyState

-- TODO this actually introduces source information, but we ideally want it to be Phantom
mono :: String -> Typed QType
mono s = let (a :< t) = runInternal initialState m in (view source (a :< t), ()) :< Mono (a :< t)
  where m :: Praxis (Typed Type)
        m = retag f <$> (parse s :: Praxis (Parsed Type))
        f :: forall a. Recursive a => I a -> Annotation Parse a -> Annotation TypeCheck a
        f i x = case i of
          IType  -> phantom KindType
          IQType -> ()

-- TODO parse qty
poly :: [Name] -> String -> Typed QType
poly vs s = let (a :< Mono t) = mono s in a :< Forall vs t

kind :: String -> Typed Kind
kind s = runInternal initialState m
  where m :: Praxis (Typed Kind)
        m = retag f <$> (parse s :: Praxis (Parsed Kind))
        f :: forall a. Recursive a => I a -> Annotation Parse a -> Annotation TypeCheck a
        f i x = case i of
          IKind  -> ()

-- TODO reduce duplication with retag

prelude :: [(Name, Typed QType, Value)]
prelude =
  [ ("add",      mono "(Int, Int) -> Int", lift (+))
  , ("sub",      mono "(Int, Int) -> Int", lift (-))
  , ("mul",      mono "(Int, Int) -> Int", lift (*))
  , ("getInt",   mono "() -> Int",         F (\(R _) -> liftIO ((L . Int) <$> readLn)))
  , ("putInt",   mono "Int -> ()",         F (\(L (Int x)) -> liftIO (print x >> pure (R Record.unit))))
  , ("putStrLn", mono "String -> ()",      F (\(L (String x)) -> liftIO (putStrLn x >> pure (R Record.unit))))
  , ("dot",      poly [ "a", "b", "c" ] "(b -> c, a -> b) -> a -> c", F (\(R r) -> case Record.unpair r of (F f, F g) -> pure (F (\x -> g x >>= f))))
  ]
  where
        lift :: (Int -> Int -> Int) -> Value
        lift f = F (\(R r) -> case Record.unpair r of (L (Int a), L (Int b)) -> pure (L (Int (f a b))))

-- TODO use parser for this
preludeKinds :: [(Name, Typed Kind)]
preludeKinds =
  [ ("Int",    kind "Type")
  , ("Bool",   kind "Type")
  , ("String", kind "Type")
  , ("Char",   kind "Type")
  , ("Share",  kind "Type -> Constraint")
  , ("->",     kind "[Type, Type] -> Type")
  ]

initialVEnv :: VEnv
initialVEnv = VEnv.fromList (map (\(n, _, v) -> (n, v)) prelude)

initialTEnv :: TEnv
initialTEnv = TEnv.fromList (map (\(n, t, _) -> (n, t)) prelude)

initialKEnv :: KEnv
initialKEnv = KEnv.fromList (map (\(a,b) -> (a, retag f b)) preludeKinds) where
  f :: forall a. Recursive a => I a -> Annotation TypeCheck a -> Annotation KindCheck a
  f i x = case i of
    IKind  -> ()

