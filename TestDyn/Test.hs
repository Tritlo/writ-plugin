{-# OPTIONS_GHC -fplugin=WRIT.Plugin
                -fplugin-opt=WRIT.Plugin:marshal-dynamics
                -dcore-lint
                 #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Main where

import WRIT.Configure
import Data.Dynamic
import Data.Maybe (mapMaybe)

k :: Dynamic -> Int
k d = fromDyn d 0

getValsOfTy :: Typeable a => [Dynamic] -> [a]
getValsOfTy = mapMaybe fromDynamic


xs :: [Dynamic]
xs = ["thanks", (), "i", False,
      "hate", (42 :: Int), "it"]

main :: IO ()
main = do print xs
          print (getValsOfTy @String xs)
      --     print $ (castDyn (1 :: Int) :: Integer)
          print $ (1 :: Int) + (toDyn (1 :: Integer))