{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE Rank2Types        #-}

module Check.Rename
  ( disambiguate
  , intro
  , introMany
  ) where

import           Check.State     (RenameState, counts, scopes)
import           Common
import           Praxis
import           Print
import           Term

import           Data.List       (nub)
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map


disambiguate :: Lens' PraxisState RenameState -> Source -> (Flavor, Name) -> Praxis Name
disambiguate state src (flavor, name) = do
  entry <- (state . scopes) `uses` Map.lookup name
  case entry of
    Just (flavor', index)
      | flavor' == flavor -> return $ name ++ "_" ++ show index
      | otherwise         -> throwAt src $ "variable " <> pretty name <> " has the wrong flavor"
    Nothing    -> throwAt src $ "variable " <> pretty name <> " is not in scope"

intro :: Lens' PraxisState RenameState -> (Flavor, Name) -> Praxis Name
intro state (flavor, name) = do
  entry <- (state . counts) `uses` Map.lookup name
  let count = case entry of { Nothing -> 0; Just count -> count }
  state . counts %= Map.insert name (count + 1)
  state . scopes %= Map.insert name (flavor, count)
  return $ name ++ "_" ++ show count

introMany :: Lens' PraxisState RenameState -> Source -> [(Flavor, Name)] -> Praxis [Name]
introMany state src vars = do
  let names = map snd vars
  when (not (isUnique names)) $ throwAt src ("variables are not distinct" :: String)
  mapM (intro state) vars
  where
    isUnique :: Eq a => [a] -> Bool
    isUnique xs = length (nub xs) == length xs
