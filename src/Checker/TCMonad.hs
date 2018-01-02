{-
 Fresh is a monad for generating fresh unification and type variables.
-}

module Checker.TCMonad
  ( TC
  , freshGreekNames
  , freshLatinNames
  , runTC
  , typeError
  , freshTyUni
  , ungeneralise
  )
where

import Control.Applicative (Applicative(..))
import Control.Monad (liftM, ap)
import Checker.Error
import Type (QType(..), Pure(..), Type(..), Constraint(..), subsType)
import Checker.Constraint (subsConstraint)


newtype TC a = TC ([String] -> Either TypeError ([String], a))

instance Functor TC where
  fmap = liftM

instance Applicative TC where
  pure x = TC (\s -> Right (s,x))
  (<*>)  = ap

instance Monad TC where
  return = pure
  (TC a) >>= f = TC (\s -> case a s of Left x -> Left x
                                       Right (s',v) -> let TC b = f v
                                                       in b s')
fresh :: String -> [String]
fresh alpha = concatMap perm [1..]
  where perm :: Int -> [String]
        perm 1 = map (:[]) alpha
        perm n = do { x <- alpha; y <- perm (n-1); return (x:y) }

freshGreekNames :: [String]
freshGreekNames = map ('~':) (fresh ['a'..'z'])
-- freshGreekNames = fresh ['α'..'ω']

freshLatinNames :: [String]
freshLatinNames = fresh ['a'..'z']

runTC :: TC a -> Either TypeError a
runTC (TC f) = fmap snd (f freshGreekNames)

typeError :: TypeError -> TC a
typeError = TC . const . Left

freshTyUni :: TC Pure
freshTyUni = TC $ \(x:xs) -> Right (xs, TyUni x)

-- TODO: Allow quantified effects
ungeneralise :: QType -> TC ([Constraint], Type)
ungeneralise (Forall cs as t) = do
  bs <- sequence (replicate (length as) freshTyUni)
  let ft = (`lookup` (zip as bs))
  let fe = const Nothing
  let subsT = subsType ft fe
  return (map (\c -> case c of Constraint s t -> Constraint s (subsT t)) cs, subsT t)
