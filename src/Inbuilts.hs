{-# LANGUAGE QuasiQuotes #-}

module Inbuilts
  ( runWithPrelude
  , integral
  , clone
  , dispose
  , copy
  , capture
  ) where

import           Check.State
import           Common
import           Introspect
import qualified Parse             (run)
import           Praxis
import           Stage
import           Term              hiding (Lit (..), Pair, Unit)

import qualified Data.Map.Strict   as Map
import           System.IO.Unsafe  (unsafePerformIO)
import           Text.RawString.QQ


runInternal :: Praxis a -> a
runInternal c = case unsafePerformIO (runPraxis (flags . silent .= True >> c)) of
  Left e  -> error ("internal computation failed: " ++ e)
  Right x -> x

kind :: String -> Annotated KindCheck Kind
kind s = cast $ runInternal (Parse.run s) where
  cast :: forall a. IsTerm a => Annotated Parse a -> Annotated KindCheck a
  cast ((src, _) :< term) = case termT :: TermT a of
    KindT -> (src, ()) :< runIdentity (recurseTerm (Identity . cast) term)

initialTypeConEnv :: TypeConEnv
initialTypeConEnv = Map.fromList
  [
  -- Types
    (mkName "Array",    kind "Type -> Type")
  , (mkName "Bool",     kind "Type")
  , (mkName "Char",     kind "Type")
  , (mkName "Fn",       kind "Type -> Type -> Type")
  , (mkName "I8",       kind "Type")
  , (mkName "I16",      kind "Type")
  , (mkName "I32",      kind "Type")
  , (mkName "I64",      kind "Type")
  , (mkName "ISize",    kind "Type")
  , (mkName "Ref",      kind "Type -> Type")
  , (mkName "String",   kind "Type")
  , (mkName "U8",       kind "Type")
  , (mkName "U16",      kind "Type")
  , (mkName "U32",      kind "Type")
  , (mkName "U64",      kind "Type")
  , (mkName "USize",    kind "Type")
  , (mkName "Unit",     kind "Type")
  , (mkName "Pair",     kind "Type -> Type -> Type")
  ]


-- TODO should be replaced with instances in prelude

integral :: Annotated TypeCheck Type -> Annotated TypeCheck TypeConstraint
integral t = phantom (TypeIsInstance (phantom (TypeApply (phantom (TypeInstance Integral)) t)))

clone :: Annotated TypeCheck Type -> Annotated TypeCheck TypeConstraint
clone t = phantom (TypeIsInstance (phantom (TypeApply (phantom (TypeInstance Clone)) t)))

dispose :: Annotated TypeCheck Type -> Annotated TypeCheck TypeConstraint
dispose t = phantom (TypeIsInstance (phantom (TypeApply (phantom (TypeInstance Dispose)) t)))

copy :: Annotated TypeCheck Type -> Annotated TypeCheck TypeConstraint
copy t = phantom (TypeIsInstance (phantom (TypeApply (phantom (TypeInstance Copy)) t)))

capture :: Annotated TypeCheck Type -> Annotated TypeCheck TypeConstraint
capture t = phantom (TypeIsInstance (phantom (TypeApply (phantom (TypeInstance Capture)) t)))

initialInstanceEnv :: InstanceEnv
initialInstanceEnv = Map.fromList
  [ (mkName "Array", Map.fromList
    [ (Clone,   \[t] -> (Native, IsInstanceOnlyIf [clone t]))
    , (Dispose, \[t] -> (Native, IsInstanceOnlyIf [dispose t]))
    ]
    )
  , (mkName "Bool", primitive)
  , (mkName "Char", primitive)
  , (mkName "Fn", Map.fromList
    [ (Clone,   \_ -> (Native, IsInstance))
    , (Dispose, \_ -> (Native, IsInstance))
    , (Copy,    \_ -> (Native, IsInstance))
    , (Capture, \_ -> (Native, IsInstance))
    ]
    )
  , (mkName "I8",    integralInst)
  , (mkName "I16",   integralInst)
  , (mkName "I32",   integralInst)
  , (mkName "I64",   integralInst)
  , (mkName "ISize", integralInst)
  , (mkName "Pair", Map.fromList
    [ (Clone,   \[a, b] -> (Trivial, IsInstanceOnlyIf [clone a, clone b]))
    , (Dispose, \[a, b] -> (Trivial, IsInstanceOnlyIf [dispose a, dispose b]))
    , (Copy,    \[a, b] -> (Trivial, IsInstanceOnlyIf [copy a, copy b]))
    , (Capture, \[a, b] -> (Trivial, IsInstanceOnlyIf [capture a, capture b]))
    ]
    )
  , (mkName "Ref", Map.fromList
    [ (Clone,   \_ -> (Trivial, IsInstance))
    , (Dispose, \_ -> (Trivial, IsInstance))
    , (Copy,    \_ -> (Trivial, IsInstance))
    ]
    )
  , (mkName "String", Map.fromList
    [ (Clone,   \_ -> (Native, IsInstance))
    , (Dispose, \_ -> (Native, IsInstance))
    ]
    )
  , (mkName "U8",    integralInst)
  , (mkName "U16",   integralInst)
  , (mkName "U32",   integralInst)
  , (mkName "U64",   integralInst)
  , (mkName "USize", integralInst)
  , (mkName "Unit", primitive)
  ] where
    primitive = Map.fromList
      [ (Clone,   \_ -> (Trivial, IsInstance))
      , (Dispose, \_ -> (Trivial, IsInstance))
      , (Copy,    \_ -> (Trivial, IsInstance))
      , (Capture, \_ -> (Trivial, IsInstance))
      ]
    integralInst = primitive `Map.union` Map.fromList
      [ (Integral, \_ -> (Native, IsInstance))
      ]


inbuilts :: [(Inbuilt, Annotated TypeCheck QType)]
inbuilts =
  [ (Add,      poly "forall a | Integral a. (a, a) -> a") -- TODO should be Num, not Integral
  , (Subtract, poly "forall a | Integral a. (a, a) -> a")
  , (Multiply, poly "forall a | Integral a. (a, a) -> a")
  , (Negate,   poly "forall a | Integral a. a -> a")
  , (GetInt,   poly "forall a | Integral a. () -> a")
  , (GetStr,   poly "() -> String")
  , (PutInt,   poly "forall a | Integral a. a -> ()")
  , (PutStr,   poly "forall &r. &r String -> ()")
  , (PutStrLn, poly "forall &r. &r String -> ()")
  , (Compose,  poly "forall a b c. (b -> c, a -> b) -> a -> c")
  , (Print,    poly "forall &r a. &r a -> ()") -- TODO should have Show constraint
  , (NewArray, poly "forall a. (USize, () -> a) -> Array a")
  , (AtArray,  poly "forall &r a. (&r Array a, USize) -> &r a")
  , (LenArray, poly "forall &r a. &r Array a -> USize")
  , (SetArray, poly "forall a. (Array a, USize, a) -> Array a")
  , (Not,      poly "Bool -> Bool")
  , (Or,       poly "(Bool, Bool) -> Bool")
  , (And,      poly "(Bool, Bool) -> Bool")
  , (Eq,       poly "forall a | Integral a. (a, a) -> Bool") -- TODO should be Eq, not Integral
  , (Neq,      poly "forall a | Integral a. (a, a) -> Bool")
  , (Lt,       poly "forall a | Integral a. (a, a) -> Bool") -- TODO should be Ord, not Integral
  , (Gt,       poly "forall a | Integral a. (a, a) -> Bool")
  , (Lte,      poly "forall a | Integral a. (a, a) -> Bool")
  , (Gte,      poly "forall a | Integral a. (a, a) -> Bool")
  ]


initialInbuiltEnv :: InbuiltEnv
initialInbuiltEnv = Map.fromList [ (mkName (show inbuilt), (inbuilt, qTy)) | (inbuilt, qTy) <- inbuilts ]

mono :: String -> Annotated TypeCheck Type
mono s = cast $ runInternal (checkState . kindState . typeConEnv .= initialTypeConEnv >> Parse.run s) where
  cast :: forall a. IsTerm a => Annotated Parse a -> Annotated TypeCheck a
  cast ((src, _) :< term) = case termT :: TermT a of
    TypeT -> (src, ()) :< runIdentity (recurseTerm (Identity . cast) term)

poly :: String -> Annotated TypeCheck QType
poly s = cast $ runInternal (checkState . kindState . typeConEnv .= initialTypeConEnv >> Parse.run s) where
  cast :: forall a. IsTerm a => Annotated Parse a -> Annotated TypeCheck a
  cast ((src, _) :< term) = case termT :: TermT a of
    TypeT           -> (src, ()) :< runIdentity (recurseTerm (Identity . cast) term)
    QTypeT          -> (src, ()) :< runIdentity (recurseTerm (Identity . cast) term)
    TypePatT        -> (src, ()) :< runIdentity (recurseTerm (Identity . cast) term)
    TypeConstraintT -> (src, ()) :< runIdentity (recurseTerm (Identity . cast) term)

runWithPrelude :: Praxis a -> IO (Either String a)
runWithPrelude c = runPraxis (importPrelude >> c) where
  importPrelude :: Praxis ()
  importPrelude = do
    checkState . instanceEnv .= initialInstanceEnv
    checkState . kindState . typeConEnv .= initialTypeConEnv
    checkState . typeState . inbuiltEnv .= initialInbuiltEnv
    flags . silent .= True
    Parse.run prelude :: Praxis (Annotated Parse Program)
    flags . silent .= False


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
