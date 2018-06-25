module Check.Env
  ( inc
  , use
  , readUse
  , intro
  , elim
  , elimN
  )
where

import Source (Source)
import Type
import Common
import Check.Derivation
import Compiler
import Error

findOver :: (a -> Maybe a) -> [a] -> Maybe [a]
findOver _ []     = Nothing
findOver f (x:xs) = case f x of
  Just y  -> Just (y : xs)
  Nothing -> (\xs -> x:xs) <$> findOver f xs

-- |Increment the usage count of a particular variable
inc :: Name -> Compiler ()
inc s = do
  l <- get tEnv
  -- TODO proper error handling here
  let Just l = findOver (\(s',(t,i)) -> if s == s' then Just (s',(t,i+1)) else Nothing) l
  set tEnv l

-- |Increment the usage count of a particular variable, and generate a Share constraint if it has already been used.
use :: Source -> Name -> Compiler (Pure, [Derivation])
use s n = do
  l <- get tEnv
  case lookup n l of
    Just (t, i) -> let cs = [ newDerivation (shareC t) ("Variable '" ++ n ++ "' used for a second time") s | i /= 0 ]
                    in inc n >> return (t, cs)
    Nothing     -> throwError (CheckError (NotInScope n s))

readUse :: Source -> Name -> Compiler (Pure, [Derivation])
readUse s n = do
  l <- get tEnv
  case lookup n l of
    Just (t, i) -> let cs = [ newDerivation (shareC t) ("Variable '" ++ n ++ "' used before let bang") s | i == 0 ]
                    in return (t, cs)
    Nothing     -> throwError (CheckError (NotInScope n s))

intro :: Name -> Pure -> Compiler ()
intro n p = over tEnv ((n, (p, 0)) :)

elim :: Source -> Compiler [Derivation]
elim s = do
  ((n, (p, i)) : l) <- get tEnv
  set tEnv l
  return [ newDerivation (dropC p) ("Variable '" ++ n ++ "' not used") s | i == 0 ]

elimN :: Int -> Source -> Compiler [Derivation]
elimN 0 _ = return []
elimN n s = do
  c1 <- elim s
  c2 <- elimN (n-1) s
  return (c1 ++ c2)
