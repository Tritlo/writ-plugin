{-# OPTIONS_GHC -fplugin=WRIT.Plugin
                -fplugin-opt=WRIT.Plugin:debug
                -ddump-ds
                 #-}

module Main where

import WRIT.Configure
import Data.Dynamic

k :: Dynamic -> Int
k d = fromDyn d 0

xs :: [Dynamic]
xs = ['b', (), False]


main :: IO ()
main = do print "hello, world"
          --print $ toDyn (2 :: Int)
        --   print $ fromDyn (2 :: Int) (undefined :: Int)
          print xs
        --   print $ k (6 :: Int)