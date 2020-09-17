{-# OPTIONS_GHC -fplugin=WRIT.Plugin
                -frefinement-level-hole-fits=1
                -fplugin-opt=WRIT.Plugin:fill-holes
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
--          print (ps _c)
