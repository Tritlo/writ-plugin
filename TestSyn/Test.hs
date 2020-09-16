{-# OPTIONS_GHC -fplugin=WRIT.Plugin
                -frefinement-level-hole-fits=2
                -fplugin-opt=WRIT.Plugin:fill-holes
 #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Main where

import WRIT.Configure
import Data.Dynamic

main :: IO ()
main = do print ((_fmap_succ :: [Int] -> [Int]) [1, 2])
