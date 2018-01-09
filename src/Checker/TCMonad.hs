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
  )
where

import Control.Applicative (Applicative(..))
import Control.Monad (liftM, ap)
import Checker.Error
import Type (Pure(..))

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

freshGreekNames = fresh ['α'..'ω']
freshLatinNames = fresh ['a'..'z']

runTC :: TC a -> Either TypeError a
runTC (TC f) = fmap snd (f freshGreekNames)

typeError :: TypeError -> TC a
typeError = TC . const . Left

freshTyUni :: TC Pure
freshTyUni = TC $ \(x:xs) -> Right (xs, TyUni x)
