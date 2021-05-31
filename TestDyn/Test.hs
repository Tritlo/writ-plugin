{-# LANGUAGE PatternSynonyms #-}
{-# OPTIONS_GHC -fplugin=WRIT.Plugin
                -fplugin-opt=WRIT.Plugin:marshal-dynamics
                -fplugin-opt=WRIT.Plugin:debug
                 #-}
                 -- -dcore-lint
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE GADTs #-}
module Main where

import WRIT.Configure
import Data.Dynamic
import Data.Maybe (mapMaybe, fromJust)
import Debug.Trace
import Unsafe.Coerce
import Data.Proxy
import Type.Reflection
import Data.Kind
import Data.Map (Map)
import qualified Data.Map as M

-- k :: Dynamic -> Int
-- k d = fromDyn d 0

-- getValsOfTy :: Typeable a => [Dynamic] -> [a]
-- getValsOfTy = mapMaybe fromDynamic

-- xs :: [Dynamic]
-- xs = ["thanks", (), "i", False,
--       "hate", (42 :: Int), "it"]

data A = A | C deriving (Show)
data B = B deriving (Show)

class Goo a where
  ok :: a -> Int

instance Goo B where
    ok _ = 9

instance Goo A where
    ok _ = 10

class Foo a where
    goo :: Int -> a -> Int
    loo :: Show a => Int -> a -> String
    foo :: a -> Int
    -- Problematic
    -- hoo :: Show a => a -> Int
    boo :: Goo a => a -> Int

instance Foo A where
    foo _ = 10
    goo x y = (ok y) + x + 1
    loo y x = show (y+5)  ++ show x


instance Foo B where
    foo _ = 20
    goo x y = (ok y) + x + 2
    loo y x = show (length (show x), y, ok x)
    -- boo x = ok x

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

--   let s = [A,B] :: [Dynamic]
--   mapM_ (print . foo) s
--   mapM_ (print . loo 2) s
  print (foo (toDyn A))
  print (foo (toDyn B))
  print (goo 1 (toDyn A))
  print (goo 3 (toDyn B))
  print (loo 5 (toDyn B))
  print (loo 2 (toDyn C))
  print (loo 2 (toDyn "OK"))