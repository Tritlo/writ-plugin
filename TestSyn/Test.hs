{-# OPTIONS_GHC -fplugin=WRIT.Plugin
                -frefinement-level-hole-fits=2
                -fplugin-opt=WRIT.Plugin:fill-holes
                -fplugin-opt=WRIT.Plugin:fill-hole-depth=2
                -dcore-lint
                -ddump-ds
 #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Main where

import WRIT.Configure
import Data.Dynamic


-- ps2 :: Show a => a -> a
-- ps2 a = a

ps :: Show a => a -> a
ps a = _
  where k :: Show b => b
        k  = _

ps3 :: Show a => a -> a
ps3 a = _
  where k :: Show a => a
        k  = k

ps8 :: a -> b -> a
ps8 a b = _

ps4 :: a -> a
ps4 a = a

ps5 :: a -> a
ps5 a = _

main :: IO ()
main = do print LT
          print $ (_fmap_succ :: [Int] -> [Int]) [1,2]
          print $ (_foldl_enumTo :: [Int] -> [Int]) [1,2]
          print (ps _)
