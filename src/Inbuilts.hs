{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs            #-}
{-# LANGUAGE Rank2Types       #-}

module Inbuilts
  ( initialState
  ) where

import           Common
import           Env
import           Introspect
import           Parse      (parse)
import           Praxis
import qualified Record
import           Term
import           Value

import           Data.List  (nub, sort)
import qualified Data.Set   as Set (empty)

-- TODO Make this importPrelude, a Monadic action?
initialState :: PraxisState
initialState = set tEnv initialTEnv $ set vEnv initialVEnv $ set kEnv initialKEnv $ set daEnv initialDAEnv $ emptyState

-- TODO this actually introduces source information, but we ideally want it to be Phantom
mono :: String -> Typed QType
mono s = let (a :< t) = runInternal initialState m in (view source (a :< t), ()) :< Mono (a :< t)
  where m :: Praxis (Typed Type)
        m = retag f <$> (parse s :: Praxis (Simple Type))
        f :: forall a. Recursive a => I a -> Annotation SimpleAnn a -> Annotation TypeAnn a
        f i x = case i of
          IType  -> phantom KindType
          IQType -> ()

-- TODO parse qty
poly :: [Name] -> String -> Typed QType
poly vs s = let (a :< Mono t) = mono s in a :< Forall vs t

kind :: String -> Typed Kind
kind s = runInternal initialState m
  where m :: Praxis (Typed Kind)
        m = cast <$> (parse s :: Praxis (Simple Kind))

prelude :: [(Name, Typed QType, Value)]
prelude =
  [ ("add",      mono "(Int, Int) -> Int", lift (+))
  , ("sub",      mono "(Int, Int) -> Int", lift (-))
  , ("mul",      mono "(Int, Int) -> Int", lift (*))
  , ("getInt",   mono "() -> Int",         F (\(R _) -> liftIO ((L . Int) <$> readLn)))
  , ("putInt",   mono "Int -> ()",         F (\(L (Int x)) -> liftIO (print x >> pure (R Record.unit))))
  , ("putStrLn", mono "String -> ()",      F (\(L (String x)) -> liftIO (putStrLn x >> pure (R Record.unit))))
  , ("dot",      poly [ "a", "b", "c" ] "(b -> c, a -> b) -> a -> c", F (\(R r) -> case Record.unpair r of (F f, F g) -> pure (F (\x -> g x >>= f))))
  , ("print",    poly [ "a" ]  "a -> ()",  F (\x -> liftIO (print x >> pure (R Record.unit)))) -- TODO should have Show constraint
  ]
  where
        lift :: (Int -> Int -> Int) -> Value
        lift f = F (\(R r) -> case Record.unpair r of { (L (Int a), L (Int b)) -> pure (L (Int (f a b))); _ -> error (show r) })

preludeKinds :: [(Name, Typed Kind)]
preludeKinds =
  [ ("Int",    kind "Type")
  , ("Bool",   kind "Type")
  , ("String", kind "Type")
  , ("Char",   kind "Type")
  , ("Affine", kind "Type -> Constraint")
  , ("Share",  kind "Type -> Constraint")
  , ("->",     kind "Type -> Type -> Type")
  ]

initialVEnv :: VEnv
initialVEnv = fromList (map (\(n, _, v) -> (n, v)) prelude)

initialTEnv :: TEnv
initialTEnv = fromList (map (\(n, t, _) -> (n, t)) prelude)

initialKEnv :: KEnv
initialKEnv = fromList (map (\(a,b) -> (a, cast b)) preludeKinds) where

initialDAEnv :: DAEnv
initialDAEnv = empty
