{-# OPTIONS_GHC -fplugin=WRIT.Plugin
                -fplugin-opt=WRIT.Plugin:debug
                -dcore-lint
                -fprint-typechecker-elaboration
                 #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Main where

import WRIT.Configure
import Data.Dynamic
import Data.Maybe (mapMaybe)

main :: IO ()
main = do print (_0 :: Bool)
