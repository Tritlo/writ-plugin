{-# OPTIONS_GHC -fplugin=WRIT.Plugin
                -fplugin-opt=WRIT.Plugin:marshal-dynamics
                -fplugin-opt=WRIT.Plugin:debug
                 #-}
                --dcore-lint

{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
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

data A = A deriving (Show)
data B = B deriving (Show)

class Foo a where
    goo :: Int -> a -> Int
    foo :: a -> Int
    -- Problematic
    -- loo :: Show a => a -> Int
    --goo :: Int -> a -> Int

instance Foo A where
    foo _ = 10
    goo x _ = 10 + x
    -- loo _ = 5

instance Foo B where
    foo _ = 20
    goo x _ = 20 + x
    -- loo _ = 7

type instance Dispatchable Foo = Msg (Text "Dispatching on Foo!")

main :: IO ()
main = do
    -- print xs

        --   print $ getValsOfTy @String xs
          let s = [A,B] :: [Dynamic]
          mapM_ (print . foo) s
          mapM_ (print . goo 5) s
        --   mapM_ (print . loo) s
        --   print (foo (toDyn A))
        --   print (foo (toDyn B))
        --   print (goo 5 (toDyn A))
        --   print (goo 6 (toDyn B))