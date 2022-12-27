{-# LANGUAGE TemplateHaskell #-}

module Syntax.TH
  ( constructorPrism
  , definePrisms
  ) where

import           Syntax.Prism

import           Control.Monad
import           Data.Char           (toLower)
import           Data.List           (find)
import           Language.Haskell.TH

gadtError :: a
gadtError = error "GADTs currently not supported."
{-# NOINLINE gadtError #-}

-- | Extract the name of a constructor, e.g. ":" or "Just".
conName :: Con -> Name
conName (NormalC name _)  =   name
conName (RecC name _)     =   name
conName (InfixC _ name _) =   name
conName (ForallC _ _ con) =   conName con
conName (GadtC _ _ _)     =   gadtError
conName (RecGadtC _ _ _)  =   gadtError

-- | Extract the types of the constructor's fields.
conFields :: Con -> [Type]
conFields (NormalC _ fields) =   map (\(_, t) -> t) fields
conFields (RecC _ fields)    =   map (\(_, _, t) -> t) fields
conFields (InfixC lhs _ rhs) =   map (\(_, t) -> t) [lhs, rhs]
conFields (ForallC _ _ con)  =   conFields con
conFields (GadtC _ _ _)      =   gadtError
conFields (RecGadtC _ _ _)   =   gadtError

-- Data dec information
data DecInfo = DecInfo Type [TyVarBndrUnit] [Con]

-- | Extract data or newtype declaration information
decInfo :: Dec -> Q DecInfo
decInfo (DataD    _ name tyVars _ cs _) =  return $ DecInfo (ConT name) tyVars cs
decInfo (NewtypeD _ name tyVars _ c _) =  return $ DecInfo (ConT name) tyVars [c]
decInfo _ = fail "partial prisms can only be derived for constructors of data type or newtype declarations."

-- | Convert tyVarBndr to type
tyVarBndrToType :: TyVarBndrUnit -> Type
tyVarBndrToType (PlainTV  n _)   = VarT n
tyVarBndrToType (KindedTV n _ k) = SigT (VarT n) k

-- | Create Prism type for specified type and conctructor fields (Prism (a, b) (CustomType a b c))
prismType :: Type -> [TyVarBndrUnit] -> [Type] -> Q Type
prismType typ tyVarBndrs fields = do
    prismCon <- [t| Prism |]
    return $ ForallT (map spec tyVarBndrs) [] $ prismCon `AppT` (applyAll typ $ map tyVarBndrToType tyVarBndrs) `AppT` (prismArgs fields) where
        spec (PlainTV n _)    = PlainTV n SpecifiedSpec
        spec (KindedTV n _ k) = KindedTV n SpecifiedSpec k

prismArgs :: [Type] -> Type
prismArgs []     = TupleT 0
prismArgs [x]    = x
prismArgs (x:xs) = AppT (AppT (TupleT 2) x) (prismArgs xs)

-- | Apply all types to supplied type
applyAll :: Type -> [Type] -> Type
applyAll = foldl AppT

-- | Construct a partial prism expression for a constructor,
-- given the constructor's name.
constructorPrism :: Name -> ExpQ
constructorPrism name = do
  DataConI n _ d    <-  reify name
  TyConI dec        <-  reify d
  DecInfo _ _ cs    <-  decInfo dec
  let Just con      =   find (\c -> n == conName c) cs
  prismFromCon (wildcard cs) con

wildcard :: [Con] -> [MatchQ]
wildcard cs
  =  if length cs > 1
     then  [match (wildP) (normalB [| Nothing |]) []]
     else  []

rename :: Name -> Name
rename n
  = mkName ('_' : nameBase n)

definePrisms :: Name -> Q [Dec]
definePrisms d = do
  TyConI dec <- reify d
  DecInfo typ tyVarBndrs cs <- decInfo dec
  join `fmap` mapM (\a -> defFromCon (wildcard cs) typ tyVarBndrs a) cs

-- | Constructs a partial prism definition for a
--   constructor, given information about the constructor.
--   The name of the partial prism is constructed by
--   spelling the constructor name with an initial lower-case
--   letter.
defFromCon :: [MatchQ] -> Type -> [TyVarBndrUnit] -> Con -> DecsQ
defFromCon matches t tyVarBndrs con = do
    let funName = rename $ conName con
    sig <- SigD funName `fmap` prismType t tyVarBndrs (conFields con)
    fun <- funD funName [ clause [] (normalB (prismFromCon matches con)) [] ]
    return [sig, fun]

-- | Constructs a partial prism expression for a
--   constructor, given information about the constructor.
prismFromCon :: [MatchQ] -> Con -> ExpQ
prismFromCon matches con = do
  let c     =   conName con
  let fs    =   conFields con
  let n     =   length fs
  (ps, vs)  <-  genPE n
  v         <-  newName "x"
  let f     =   lamE [nested tupP ps] (foldl appE (conE c) vs)
  let g     =   lamE [varP v]
                  (caseE (varE v) $
                    [ match (conP c ps)
                        (normalB [| Just $(nested tupE vs) |]) []
                    ] ++ matches)
  [| Prism $f $g |]

genPE :: Int -> Q ([PatQ], [ExpQ])
genPE n = do
  ids <- replicateM n (newName "x")
  return (map varP ids, map varE ids)

nested :: ([t] -> t) -> [t] -> t
nested tup []     =  tup []
nested _   [x]    =  x
nested tup (x:xs) =  tup [x, nested tup xs]
