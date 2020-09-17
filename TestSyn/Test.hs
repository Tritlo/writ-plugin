{-# OPTIONS_GHC -fplugin=WRIT.Plugin
                -frefinement-level-hole-fits=0
                -fplugin-opt=WRIT.Plugin:fill-holes
 #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Main where

import WRIT.Configure
import Data.Dynamic

ps :: Show a => a -> a
ps a = _a


main :: IO ()
main = do --print LT
          print (_b)
--          print (ps _c)
