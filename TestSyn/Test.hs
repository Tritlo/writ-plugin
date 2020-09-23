{-# OPTIONS_GHC -fplugin=WRIT.Plugin
                -frefinement-level-hole-fits=2
                -fplugin-opt=WRIT.Plugin:fill-holes
                -fplugin-opt=WRIT.Plugin:fill-hole-depth=1
                -dcore-lint
 #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Main where

import WRIT.Configure
import Data.Dynamic

ps :: Show a => a -> a
ps a = _
  where k :: Show b => b
        k  = _

isOdd :: Integer -> Bool
isOdd arg = not _even_arg
  where myEven :: Integer -> Bool
        myEven 0 = True
        myEven n = _ (n-1)


f :: b -> a -> b
f = const
g :: a -> b -> b
g = _fli


ps8 :: a -> b -> a
ps8 a b = _


ps5 :: a -> a
ps5 a = _

main :: IO ()
main = do print LT
          print (g 2 3)
          print $ isOdd 5
          print $ (_fmap_succ :: [Int] -> [Int]) [1,2]
          print $ (_foldl_enumTo :: [Int] -> [Int]) [1,2]
          print (ps _)
