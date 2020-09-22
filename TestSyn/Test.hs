{-# OPTIONS_GHC -fplugin=WRIT.Plugin
                -frefinement-level-hole-fits=2
                -fplugin-opt=WRIT.Plugin:fill-holes
                -fplugin-opt=WRIT.Plugin:fill-hole-depth=1
 #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Main where

import WRIT.Configure
import Data.Dynamic

ps :: Show a => a -> a
ps a = _

main :: IO ()
main = do --print LT
          print $ (_fmap_succ :: [Int] -> [Int]) [1,2]
          print $ (_foldl :: [Int] -> [Int]) [1,2]
--          print (ps _c)
