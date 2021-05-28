{-# OPTIONS_GHC -fplugin=WRIT.Plugin
                -fplugin-opt=WRIT.Plugin:marshal-dynamics
                -fplugin-opt=WRIT.Plugin:debug
                -dcore-lint
                 #-}
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

data A = A deriving (Typeable, Show)
data B = B deriving (Typeable, Show)

class Typeable a => Foo a where
    goo :: a -> Int -> Int
    foo :: a -> Int
    -- Problematic
    --foo :: Show a => a -> Int
    --goo :: Int -> a -> Int

instance Foo A where
    foo _ = 10
    goo _ x = 10 + x

instance Foo B where
    foo _ = 20
    goo _ x = 20 + x

-- dynFoo :: Dynamic -> Int
-- dynFoo d =
--     case dynTypeRep d of
--         x | x == someTypeRep (Proxy @A) -> (foo @A) $ fromDyn d undefined
--         x | x == someTypeRep (Proxy @B) -> (foo @B) $ fromDyn d undefined
--         x -> undefined

insts  :: [(SomeTypeRep,Dynamic)]
insts  = [(SomeTypeRep (typeRep :: TypeRep A), toDyn (foo @A))
         ,(SomeTypeRep (typeRep :: TypeRep B), toDyn (foo @B))]

type instance Dispatchable Foo = Msg (Text "Dispatching on Foo!")

-- instance Foo Dynamic where
--   foo = dynDispatch insts "foo"
--   goo x d = (dynDispatch insts "goo") d x

main :: IO ()
main = do
    -- print xs

        --   print $ getValsOfTy @String xs
          --   mapM_ (print . foo) s
        --   let s = [A,B] :: [Dynamic]
          print (goo (toDyn A) 5)
          print (goo (toDyn B) 6)