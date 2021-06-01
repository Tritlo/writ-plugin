{-# LANGUAGE PatternSynonyms #-}
{-# OPTIONS_GHC -fplugin=WRIT.Plugin
                -fplugin-opt=WRIT.Plugin:marshal-dynamics
                -fplugin-opt=WRIT.Plugin:debug
                -dcore-lint
                 #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE GADTs #-}
module Main where

import WRIT.Configure
import Data.Dynamic
-- import Data.Maybe (mapMaybe, fromJust)
-- import Debug.Trace
-- import Unsafe.Coerce
-- import Data.Proxy
-- import Type.Reflection
-- import Data.Kind
-- import Data.Map (Map)
-- import qualified Data.Map as M

-- k :: Dynamic -> Int
-- k d = fromDyn d 0

-- getValsOfTy :: Typeable a => [Dynamic] -> [a]
-- getValsOfTy = mapMaybe fromDynamic

-- xs :: [Dynamic]
-- xs = ["thanks", (), "i", False,
--       "hate", (42 :: Int), "it"]

data A = A | B deriving (Show)
data C = C deriving (Show)

class Foo a where
   foo :: a -> Int
   insts :: Show a => a -> String

instance Foo A where
    foo _ = 10
    insts x = "A: " ++ show x

instance Foo C where
    foo _ = 20
    insts x = "C: " ++ show x
pattern Is :: forall a. (Typeable a) => a -> Dynamic
pattern Is res <- (fromDynamic @a -> Just res)

main :: IO ()
main = do

  print $ case C of
            Is A -> "was A"
            Is B -> "was B"
            Is C -> "was C"
            x -> error (show x)
  print $ case toDyn A of
             Is (x :: A) -> "was " ++ show x
             Is B -> "was B"
             x -> error (show x)

  let s = [A,B,C] :: [Dynamic]
  mapM_ (print . foo) s
  mapM_ (print . insts) s

