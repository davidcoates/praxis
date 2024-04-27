{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs            #-}
{-# LANGUAGE QuasiQuotes      #-}
{-# LANGUAGE Rank2Types       #-}

module Inbuilts
  ( initialState
  , integral
  ) where

import           Common
import qualified Env.Env                   as Env
import qualified Env.LEnv                  as LEnv
import           Introspect
import           Parse                     (parse)
import           Praxis
import           Term                      hiding (Lit (..), Pair, Unit)
import           Value

import           Control.Monad.Trans.Class (MonadTrans (..))
import qualified Control.Monad.Trans.State as State (get)
import qualified Data.Set                  as Set
import           Text.RawString.QQ

-- Include inbuilt kinds
initialState0 :: PraxisState
initialState0 = set dtEnv initialDTEnv $ set kEnv initialKEnv $ emptyState

-- Include inbuilts
initialState1 :: PraxisState
initialState1 = set vEnv initialVEnv $ set tEnv initialTEnv $ initialState0

-- TODO Make this importPrelude, a Monadic action?
initialState :: PraxisState
initialState = fixup (runInternal initialState1 ((parse prelude :: Praxis (Annotated Program)) >> lift State.get)) where
  -- TODO a nicer way to do this. Undo all the things except the fields we care about.
  fixup = set flags (view flags emptyState) . set fresh (view fresh emptyState) . set stage (view stage emptyState) . set kindSystem (view kindSystem emptyState) . set tySystem initialTySystem

mono :: String -> Annotated Type
mono s = runInternal initialState0 (parse s :: Praxis (Annotated Type))

poly :: String -> Annotated QType
poly s = runInternal initialState0 (parse s :: Praxis (Annotated QType))

kind :: String -> Annotated Kind
kind s = runInternal emptyState (parse s :: Praxis (Annotated Kind))

inbuilts :: [(Name, Annotated QType, Value)]
inbuilts =
  [ ("add"
    , poly "forall a | Integral a . (a, a) -> a" -- TODO should be Num, not Integral
    , liftIII (+)
    )
  , ("subtract"
    , poly "forall a | Integral a . (a, a) -> a"
    , liftIII (-)
    )
  , ("multiply"
    , poly "forall a | Integral a . (a, a) -> a"
    , liftIII (*)
    )
  , ("negate"
    , poly "forall a | Integral a . a -> a"
    , liftI $ \(con, decon) -> Fun (\x -> return (con (negate (decon x))))
    )
  , ("get_int"
    , poly "forall a | Integral a . () -> a"
    , liftI $ \(con, decon) -> Fun (\Unit -> liftIOUnsafe (con <$> readLn))
    )
  , ("get_str"
    , poly "() -> String"
    , Fun (\Unit -> Value.String <$> liftIOUnsafe getContents)) -- TODO need to make many of these functions strict?
  , ("put_int"
    , poly "forall a | Integral a. a -> ()"
    , liftI $ \(_, decon) -> Fun (\i -> liftIOUnsafe (print (decon i) >> pure Unit))
    )
  , ("put_str"
    , poly "forall &r. &r String -> ()"
    , Fun (\(String s) -> liftIOUnsafe (putStr s) >> pure Unit)
    )
  , ("put_str_ln"
    , poly "forall &r. &r String -> ()"
    , Fun (\(String s) -> liftIOUnsafe (putStrLn s) >> pure Unit)
    )
  , ("compose"
    , poly "forall a b c. (b -> c, a -> b) -> a -> c"
    , Fun (\(Pair (Fun f) (Fun g)) -> pure (Fun (\x -> g x >>= f)))
    )
  , ("print"
    , poly "forall &r a. &r a -> ()" -- TODO should have Show constraint
    , Fun (\x -> liftIOUnsafe (print x >> pure Unit))
    )
  , ("new_array"
    , poly "forall a. (USize, () -> a) -> Array a"
    , Fun (\(Pair (USize i) v) -> Value.newArray i v)
    )
  , ("at_array"
    , poly "forall &r a. (&r Array a, USize) -> &r a"
    , Fun (\(Pair (Array a) (USize i)) -> Value.readArray a i)
    )
  , ("len_array"
    , poly "forall &r a. &r Array a -> USize"
    , Fun (\(Array a) -> USize <$> Value.lenArray a)
    )
  , ("set_array"
    , poly "forall a. (Array a, USize, a) -> Array a"
    , Fun (\(Pair (Array a) (Pair (USize i) e)) -> Value.writeArray a i e >> pure (Array a))
    )
  , ("not"
    , poly "Bool -> Bool"
    , Fun (\(Bool a) -> pure (Bool (not a)))
    )
  , ("or"
    , poly "(Bool, Bool) -> Bool"
    , liftBBB (||)
    )
  , ("and"
    , poly "(Bool, Bool) -> Bool"
    , liftBBB (&&))
  , ("eq"
    , poly "forall a | Integral a . (a, a) -> Bool" -- TODO should be Eq, not Integral
    , liftIIB (==)
    )
  , ("neq"
    , poly "forall a | Integral a . (a, a) -> Bool"
    , liftIIB (/=)
    )
  , ("lt"
    , poly "forall a | Integral a . (a, a) -> Bool" -- TODO should be Ord, not Integral
    , liftIIB (<)
    )
  , ("gt"
    , poly "forall a | Integral a . (a, a) -> Bool"
    , liftIIB (>)
    )
  , ("lte"
    , poly "forall a | Integral a . (a, a) -> Bool"
    , liftIIB (<=)
    )
  , ("gte"
    , poly "forall a | Integral a . (a, a) -> Bool"
    , liftIIB (>=)
    )
  ]
  where
    liftI :: ((Integer -> Value, Value -> Integer) -> Value) -> Value
    liftI f = Polymorphic $ \[(_, _ :< TyCon ty)] -> f (integerToValue ty, valueToInteger)
    liftII :: (forall a. Integral a => (a -> a)) -> Value
    liftII f = liftI $ \(con, decon) -> Fun (\x -> return (con (f (decon x))))
    liftIII :: (forall a. Integral a => (a -> a -> a)) -> Value
    liftIII f = liftI $ \(con, decon) -> Fun (\(Pair x y) -> return (con (f (decon x) (decon y))))
    liftIIB :: (forall a. Integral a => (a -> a -> Bool)) -> Value
    liftIIB f = liftI $ \(con, decon) -> Fun (\(Pair x y) -> return (Bool (f (decon x) (decon y))))
    liftBBB :: (Bool -> Bool -> Bool) -> Value
    liftBBB f = Fun (\(Pair (Bool a) (Bool b)) -> pure (Bool (f a b)))

inbuiltKinds :: [(Name, Annotated Kind)]
inbuiltKinds =
  [
  -- Types
    ("Array",    kind "Type -> Type")
  , ("Bool",     kind "Type")
  , ("Char",     kind "Type")
  , ("I8",       kind "Type")
  , ("I16",      kind "Type")
  , ("I32",      kind "Type")
  , ("I64",      kind "Type")
  , ("ISize",    kind "Type")
  , ("String",   kind "Type")
  , ("U8",       kind "Type")
  , ("U16",      kind "Type")
  , ("U32",      kind "Type")
  , ("U64",      kind "Type")
  , ("USize",    kind "Type")
  -- Constraints
  , ("Copy",     kind "Type -> Constraint")
  , ("Integral", kind "Type -> Constraint")
  ]

-- TODO very gross, should be replaced with instances in prelude
integral :: Annotated Type -> TyConstraint
integral t = Class (TyApply (TyCon "Integral" `as` phantom (KindFun (phantom KindType) (phantom KindConstraint))) t `as` phantom KindType)

initialDTEnv :: DTEnv
initialDTEnv = Env.fromList
  [ ("Array",  \(Just _) -> CanNotCopy)
  , ("Bool",   \Nothing  -> CanCopy)
  , ("Char",   \Nothing  -> CanCopy)
  , ("I8",     \Nothing  -> CanCopy)
  , ("I16",    \Nothing  -> CanCopy)
  , ("I32",    \Nothing  -> CanCopy)
  , ("I64",    \Nothing  -> CanCopy)
  , ("ISize",  \Nothing  -> CanCopy)
  , ("U8",     \Nothing  -> CanCopy)
  , ("U16",    \Nothing  -> CanCopy)
  , ("U32",    \Nothing  -> CanCopy)
  , ("U64",    \Nothing  -> CanCopy)
  , ("USize",  \Nothing  -> CanCopy)
  , ("String", \Nothing  -> CanNotCopy)
  ]

initialKEnv :: KEnv
initialKEnv = Env.fromList inbuiltKinds

initialTEnv :: TEnv
initialTEnv = LEnv.fromList (map (\(n, t, _) -> (n, t)) inbuilts)

initialVEnv :: VEnv
initialVEnv = Env.fromList (map (\(n, _, v) -> (n, v)) inbuilts)

initialTySystem :: System TyConstraint
initialTySystem = System
  { _requirements = []
  , _assumptions = Set.fromList [ integral (TyCon n `as` phantom KindType) | n <- [ "I8", "I16", "I32", "I64", "ISize", "U8", "U16", "U32", "U64", "USize" ] ]
  }

-- TODO interfaces
prelude = [r|

-- Operators
operator (_ + _) = add where
  left associative

operator (_ - _) = subtract where
  left associative
  precedence equal (_ + _)

operator (_ * _) = multiply where
  left associative
  precedence above (_ + _)

operator (- _) = negate where
  precedence above (_ * _)

operator (_ . _) = compose where
  right associative

operator (_ [ _ ]) = at_array

operator (_ [ _ ] <- _) = set_array

operator (! _) = not

operator (_ && _) = and where
  left associative
  precedence below (! _)

operator (_ || _) = or where
  left associative
  precedence below (_ && _)

operator (_ == _) = eq where
  precedence below (_ + _)

operator (_ != _) = neq where
  precedence equal (_ == _)

operator (_ < _) = lt where
  precedence equal (_ == _)

operator (_ > _) = gt where
  precedence equal (_ == _)

operator (_ <= _) = lte where
  precedence equal (_ == _)

operator (_ >= _) = gte where
  precedence equal (_ == _)

|]
