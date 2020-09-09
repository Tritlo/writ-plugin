{-# OPTIONS_GHC -fplugin=WRIT.Plugin
                -fplugin-opt=WRIT.Plugin:debug
                -ddump-ds
                 #-}

module Main where

import WRIT.Configure
import Data.Dynamic

k :: Dynamic -> Int
k d = fromDyn d 0

main :: IO ()
main = do print "hello, world"
          print $ toDyn (2 :: Int)
          print $ fromDyn (2 :: Int) (1 :: Int)