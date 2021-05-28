{-# OPTIONS_GHC -fplugin=WRIT.Plugin
                -fplugin-opt=WRIT.Plugin:marshal-dynamics
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

k :: Dynamic -> Int
k d = fromDyn d 0

getValsOfTy :: Typeable a => [Dynamic] -> [a]
getValsOfTy = mapMaybe fromDynamic

xs :: [Dynamic]
xs = ["thanks", (), "i", False,
      "hate", (42 :: Int), "it"]

data A = A deriving (Typeable)
data B = B deriving (Typeable)

class Typeable a => Foo a where
    foo :: a -> Int
    goo :: a -> Int -> Int

instance Foo A where
    foo _ = 10

instance Foo B where
    foo _ = 20

-- dynFoo :: Dynamic -> Int
-- dynFoo d =
--     case dynTypeRep d of
--         x | x == someTypeRep (Proxy @A) -> (foo @A) $ fromDyn d undefined
--         x | x == someTypeRep (Proxy @B) -> (foo @B) $ fromDyn d undefined
--         x -> undefined

insts  :: Map (String, SomeTypeRep) Dynamic
insts  = M.fromList [(("foo", someTypeRep (Proxy @A)), toDyn (foo @A))
                    ,(("foo", someTypeRep (Proxy @B)), toDyn (foo @B))]

instance Dispatchable Foo where


main :: IO ()
main = do print xs

          print $ getValsOfTy @String xs
        --   let s = [A,B] :: [Dynamic]
        --   print ((dispatch insts "foo" A) @Int)
        --   print ((dispatch insts "foo" B) @Int)

        --   print $ (((1 :: Int) :: Dynamic) :: Integer)
        --   print $ (1 :: Int) + (toDyn ('a'))