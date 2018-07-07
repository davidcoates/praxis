module Sub
  ( Sub(..)
  , Term(..)
  ) where

import           Effect
import           Type

data Term = TermPure Pure
          | TermEffects Effects
  deriving (Ord, Eq)

instance Show Term where
  show (TermPure p)    = show p
  show (TermEffects e) = show e

class Sub a where
  sub :: (Name -> Maybe Term) -> a -> a

  subP :: (Name -> Maybe Pure) -> a -> a
  subP f = sub (\n -> TermPure <$> f n)
  subE :: (Name -> Maybe Effects) -> a -> a
  subE f = sub (\n -> TermEffects <$> f n)

instance Sub Pure where
  sub f (TyBang    p) = sub f p
  sub f (TyData i ps) = TyData i (map (sub f) ps)
  sub f (TyFun p1 t2) = TyFun (sub f p1) (sub f t2)
  sub f (TyPrim p)    = TyPrim p
  sub f (TyRecord r)  = TyRecord (fmap (sub f) r)
  sub f t             = case t of
    TyUni n -> g (TyUni n) n
    TyVar n -> g (TyVar n) n
    where g t n | Just (TermPure p) <- f n = p
                | Nothing           <- f n = t
                | otherwise                = error "Bad term substitution"

instance Sub Impure where
  sub f (p :# e) = sub f p :# sub f e

instance Sub Constraint where
  sub f (Class c p)    = Class c (sub f p)
  sub f (EqualE e1 e2) = EqualE (sub f e1) (sub f e2)
  sub f (EqualP p1 p2) = EqualP (sub f p1) (sub f p2)

instance Sub Type where
  sub f (Mono t) = Mono (sub f t)
  sub f t        = t

instance Sub Term where
  sub f (TermPure p)    = TermPure $ sub f p
  sub f (TermEffects e) = TermEffects $ sub f e

instance Sub Effects where
  sub f es = Effect.fromList $ concatMap h (Effect.toList es)
    where h (EfUni n) = g (EfUni n) n
          h (EfVar n) = g (EfVar n) n
          h e         = [e]
          g :: Effect -> Name -> [Effect]
          g e n | Just (TermEffects e) <- f n = Effect.toList e
                | Nothing              <- f n = [e]
                | otherwise                   = error "Bad term substitution"

instance Sub a => Sub [a] where
  sub f = map (sub f)

