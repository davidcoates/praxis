{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs            #-}
{-# LANGUAGE Rank2Types       #-}

module Inbuilts
  ( initialState
  ) where

import           Common
import           Env
import           Introspect
import           Parse                    (parse)
import           Praxis
import           Term
import qualified Text.Earley.Mixfix.Graph as Earley
import           Value

import           Data.Array               (array)
import           Data.List                (nub, sort)
import qualified Data.Map.Strict          as Map (empty, fromList)
import qualified Data.Set                 as Set (empty)
import qualified Text.Earley.Mixfix       as Earley
import qualified Text.Earley.Mixfix.Graph as Earley

-- TODO Make this importPrelude, a Monadic action?
initialState :: PraxisState
initialState = set opContext initialOpContext $ set tEnv initialTEnv $ set vEnv initialVEnv $ set kEnv initialKEnv $ set daEnv initialDAEnv $ emptyState

-- TODO this actually introduces source information, but we ideally want it to be Phantom
mono :: String -> Annotated QType
mono s = let (a :< t) = runInternal initialState m in (view source (a :< t), Nothing) :< Mono (a :< t)
  where m :: Praxis (Annotated Type)
        m = retag f <$> (parse s :: Praxis (Annotated Type))
        f :: forall a. Term a => I a -> Maybe (Annotation a) -> Maybe (Annotation a)
        f i Nothing = case i of
          IType  -> Just (phantom KindType)
          IQType -> Nothing

-- TODO parse qty
poly :: [Name] -> String -> Annotated QType
poly vs s = let (a :< Mono t) = mono s in a :< Forall (map QTyVar vs) t

kind :: String -> Annotated Kind
kind s = runInternal initialState (parse s :: Praxis (Annotated Kind))

prelude :: [(Name, Annotated QType, Value)]
prelude =
  [ ("add" ,     mono "(Int, Int) -> Int", lift (+))
  , ("subtract", mono "(Int, Int) -> Int", lift (-))
  , ("multiply", mono "(Int, Int) -> Int", lift (*))
  , ("negate",   mono "Int -> Int", F (\(L (Int x)) -> pure (L (Int (negate x)))))
  , ("getInt",   mono "() -> Int",         F (\U -> liftIO ((L . Int) <$> readLn)))
  , ("putInt",   mono "Int -> ()",         F (\(L (Int x)) -> liftIO (print x >> pure U)))
  , ("putStrLn", mono "String -> ()",      F (\(L (String x)) -> liftIO (putStrLn x >> pure U)))
  , ("compose",  poly [ "a", "b", "c" ] "(b -> c, a -> b) -> a -> c", F (\(P (F f) (F g)) -> pure (F (\x -> g x >>= f))))
  , ("print",    poly [ "a" ]  "a -> ()",  F (\x -> liftIO (print x >> pure U))) -- TODO should have Show constraint
  ]
  where
    lift :: (Int -> Int -> Int) -> Value
    lift f = F (\(P (L (Int a)) (L (Int b))) -> pure (L (Int (f a b))))

preludeKinds :: [(Name, Annotated Kind)]
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
initialKEnv = fromList preludeKinds

initialDAEnv :: DAEnv
initialDAEnv = empty

preludeOps = unlines $
  [ "operator (_ + _) = add where"
  , "  associates left"
  , ""
  , "operator (_ - _) = subtract where"
  , "  associates left"
  , "  precedence equal (_ + _)"
  , ""
  , "operator (_ * _) = multiply where"
  , "  associates left"
  , "  precedence above (_ + _)"
  , ""
  , "operator (- _) = negate where"
  , "  precedence above (_ * _)"
  , ""
  , "operator (_ . _) = compose where"
  , "  associates right"
  ]

initialOpContext :: OpContext
initialOpContext = runInternal (set opContext emptyOpContext $ set vEnv initialVEnv $ emptyState) ((parse preludeOps :: Praxis (Annotated Program)) >> use opContext)

emptyOpContext :: OpContext
emptyOpContext = OpContext { _defns = Map.empty, _levels = [], _table = Earley.OpTable { Earley.precedence = array (1, 0) [], Earley.table = array (1, 0) [] } }
