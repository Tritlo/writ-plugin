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

-- data A = A | B
-- data C = C


isWithDyn :: IO ()
isWithDyn = print $ case toDyn A of
             Is A -> "was 1A"
             Is B -> "was 1B"
             Is C -> "was 1C"
             _ -> undefined

isDirect ::  IO ()
isDirect = print $ case C of
             Is A -> "was 2A"
             Is B -> "was 2B"
             Is C -> "was 2C"
             _ -> undefined

main :: IO ()
main = do

  let s = [A,B,C] :: [Dynamic]
  mapM print s
  mapM_ (print . foo) s
  mapM_ (print . insts) s
  let a = A :: Dynamic
  print (a :: A)

  isWithDyn
  isDirect
