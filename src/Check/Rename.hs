{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE Rank2Types        #-}

module Check.Rename
  ( disambiguate
  , intro
  , introMany
  ) where

import           Check.State
import           Common
import           Praxis
import           Print

import           Data.List       (nub)
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map


disambiguate :: Lens' PraxisState (State c) -> Source -> Name -> Praxis Name
disambiguate state src name = do
  entry <- (state . scopes) `uses` Map.lookup name
  case entry of
    Just scope -> return $ name ++ "_" ++ show scope
    Nothing    -> throwAt src $ "variable " <> quote (pretty name) <> " is not in scope"

intro :: Lens' PraxisState (State c) -> Name -> Praxis Name
intro state name = do
  entry <- (state . counts) `uses` Map.lookup name
  let count = case entry of { Nothing -> 0; Just count -> count }
  state . counts %= Map.insert name (count + 1)
  state . scopes %= Map.insert name count
  return $ name ++ "_" ++ show count

introMany :: Lens' PraxisState (State c) -> Source -> [Name] -> Praxis [Name]
introMany state src names = do
  when (not (isUnique names)) $ throwAt src ("variables are not distinct" :: String)
  mapM (intro state) names
  where
    isUnique :: Eq a => [a] -> Bool
    isUnique xs = length (nub xs) == length xs

