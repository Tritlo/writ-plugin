{-# OPTIONS_GHC -fplugin=WRIT.Plugin
                -frefinement-level-hole-fits=0
                -fplugin-opt=WRIT.Plugin:fill-holes
                -ddump-ds
 #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Main where

import WRIT.Configure
import Data.Dynamic

ps :: Show a => a -> a
ps a = _


main :: IO ()
main = do --print LT
          print (_)
          print (ps _)
