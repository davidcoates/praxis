{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs            #-}
{-# LANGUAGE QuasiQuotes      #-}
{-# LANGUAGE Rank2Types       #-}

module Inbuilts
  ( initialState
  , fn
  , unit
  , pair
  , integral
  , clone
  , cloneTrivial
  , dispose
  , disposeTrivial
  , copy
  ) where

import           Common
import qualified Env.Env                   as Env
import qualified Env.LEnv                  as LEnv
import           Introspect
import           Parse                     (parse)
import           Praxis
import           Term                      hiding (Lit (..), Pair, Unit)

import           Control.Monad.Trans.Class (MonadTrans (..))
import qualified Control.Monad.Trans.State as State (get)
import           Data.Map.Strict           (Map)
import qualified Data.Map.Strict           as Map
import qualified Data.Set                  as Set
import           Text.RawString.QQ

-- Include inbuilt kinds
initialState0 :: PraxisState
initialState0 = set iEnv initialIEnv $ set kEnv initialKEnv $ emptyState

-- Include inbuilts
initialState1 :: PraxisState
initialState1 = set tEnv initialTEnv $ initialState0

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

inbuilts :: [(Name, Annotated QType)]
inbuilts =
  [ ("add"
    , poly "forall a | Integral a . (a, a) -> a" -- TODO should be Num, not Integral
    )
  , ("subtract"
    , poly "forall a | Integral a . (a, a) -> a"
    )
  , ("multiply"
    , poly "forall a | Integral a . (a, a) -> a"
    )
  , ("negate"
    , poly "forall a | Integral a . a -> a"
    )
  , ("get_int"
    , poly "forall a | Integral a . () -> a"
    )
  , ("get_str"
    , poly "() -> String"
    )
  , ("put_int"
    , poly "forall a | Integral a. a -> ()"
    )
  , ("put_str"
    , poly "forall &r. &r String -> ()"
    )
  , ("put_str_ln"
    , poly "forall &r. &r String -> ()"
    )
  , ("compose"
    , poly "forall a b c. (b -> c, a -> b) -> a -> c"
    )
  , ("print"
    , poly "forall &r a. &r a -> ()" -- TODO should have Show constraint
    )
  , ("new_array"
    , poly "forall a. (USize, () -> a) -> Array a"
    )
  , ("at_array"
    , poly "forall &r a. (&r Array a, USize) -> &r a"
    )
  , ("len_array"
    , poly "forall &r a. &r Array a -> USize"
    )
  , ("set_array"
    , poly "forall a. (Array a, USize, a) -> Array a"
    )
  , ("not"
    , poly "Bool -> Bool"
    )
  , ("or"
    , poly "(Bool, Bool) -> Bool"
    )
  , ("and"
    , poly "(Bool, Bool) -> Bool"
    )
  , ("eq"
    , poly "forall a | Integral a . (a, a) -> Bool" -- TODO should be Eq, not Integral
    )
  , ("neq"
    , poly "forall a | Integral a . (a, a) -> Bool"
    )
  , ("lt"
    , poly "forall a | Integral a . (a, a) -> Bool" -- TODO should be Ord, not Integral
    )
  , ("gt"
    , poly "forall a | Integral a . (a, a) -> Bool"
    )
  , ("lte"
    , poly "forall a | Integral a . (a, a) -> Bool"
    )
  , ("gte"
    , poly "forall a | Integral a . (a, a) -> Bool"
    )
  ]

inbuiltKinds :: [(Name, Annotated Kind)]
inbuiltKinds =
  [
  -- Types
    ("Array",    kind "Type -> Type")
  , ("Bool",     kind "Type")
  , ("Char",     kind "Type")
  , ("Fn",       kind "(Type, Type) -> Type")
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
  , ("Unit",     kind "Type")
  , ("Pair",     kind "(Type, Type) -> Type")
  -- Constraints
  , ("Clone",          kind "Type -> Constraint")
  , ("TrivialClone",   kind "Type -> Constraint")
  , ("Dispose",        kind "Type -> Constraint")
  , ("TrivialDispose", kind "Type -> Constraint")
  , ("Copy",           kind "Type -> Constraint")
  , ("Integral",       kind "Type -> Constraint")
  ]

fn :: Annotated Type -> Annotated Type -> Annotated Type
fn a b = TyApply (TyCon "Fn" `as` kind "(Type, Type) -> Type") (TyPack a b `as` kind "(Type, Type)") `as` kind "Type"

unit :: Annotated Type
unit = TyCon "Unit" `as` kind "Type"

pair :: Annotated Type -> Annotated Type -> Annotated Type
pair a b = TyApply (TyCon "Pair" `as` kind "(Type, Type) -> Type") (TyPack a b `as` kind "(Type, Type)") `as` kind "Type"

-- TODO should be replaced with instances in prelude

integral :: Annotated Type -> Annotated Type
integral t = TyApply (TyCon "Integral" `as` kind "Type -> Constraint") t `as` kind "Type"

clone :: Annotated Type -> Annotated Type
clone t = TyApply (TyCon "Clone" `as` kind "Type -> Constraint") t `as` kind "Type"

cloneTrivial :: Annotated Type -> Annotated Type
cloneTrivial t = TyApply (TyCon "CloneTrivial" `as` kind "Type -> Constraint") t `as` kind "Type"

dispose :: Annotated Type -> Annotated Type
dispose t = TyApply (TyCon "Dispose" `as` kind "Type -> Constraint") t `as` kind "Type"

disposeTrivial :: Annotated Type -> Annotated Type
disposeTrivial t = TyApply (TyCon "DisposeTrivial" `as` kind "Type -> Constraint") t `as` kind "Type"

copy :: Annotated Type -> Annotated Type
copy t = TyApply (TyCon "Copy" `as` kind "Type -> Constraint") t `as` kind "Type"

initialIEnv :: IEnv
initialIEnv = Env.fromList
  [ ("Array", Map.fromList
    [ ("Clone",   \(Just t) -> (Inbuilt, IsInstanceOnlyIf [clone t]))
    , ("Dispose", \(Just t) -> (Inbuilt, IsInstanceOnlyIf [dispose t]))
    ]
    )
  , ("Bool",  primitive)
  , ("Char",  primitive)
  , ("Fn", Map.fromList
    [ ("Clone",   \(Just _) -> (Inbuilt, IsInstance))
    , ("Dispose", \(Just _) -> (Inbuilt, IsInstance))
    , ("Copy"   , \(Just _) -> (Inbuilt, IsInstance))
    ]
    )
  , ("I8",    integral)
  , ("I16",   integral)
  , ("I32",   integral)
  , ("I64",   integral)
  , ("ISize", integral)
  , ("U8",    integral)
  , ("U16",   integral)
  , ("U32",   integral)
  , ("U64",   integral)
  , ("USize", integral)
  , ("Unit", Map.fromList
    [ ("Clone",          \(Just _) -> (Trivial, IsInstance))
    , ("Dispose",        \(Just _) -> (Trivial, IsInstance))
    , ("Copy",           \(Just _) -> (Trivial, IsInstance))
   ]
    )
  , ("Pair", Map.fromList
    [ ("Clone",          \(Just (_ :< TyPack a b)) -> (Trivial, IsInstanceOnlyIf [clone a, clone b]))
    , ("Dispose",        \(Just (_ :< TyPack a b)) -> (Trivial, IsInstanceOnlyIf [dispose a, dispose b]))
    , ("Copy",           \(Just (_ :< TyPack a b)) -> (Trivial, IsInstanceOnlyIf [copy a, copy b]))
    ]
    )
  , ("String", Map.fromList
    [ ("Clone",   \Nothing -> (Inbuilt, IsInstance))
    , ("Dispose", \Nothing -> (Inbuilt, IsInstance))
    ]
    )
  ] where
    primitive = Map.fromList
      [ ("Clone",          \Nothing -> (Trivial, IsInstance))
      , ("Dispose",        \Nothing -> (Trivial, IsInstance))
      , ("Copy",           \Nothing -> (Trivial, IsInstance))
      ]
    integral = primitive `Map.union` Map.fromList
      [ ("Integral", \Nothing -> (Inbuilt, IsInstance))
      ]

initialKEnv :: KEnv
initialKEnv = Env.fromList inbuiltKinds

initialTEnv :: TEnv
initialTEnv = LEnv.fromList inbuilts

initialTySystem :: System TyConstraint
initialTySystem = System
  { _requirements = []
  , _assumptions = Set.empty
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
