{-# OPTIONS_GHC -fplugin KindDefaults.Plugin -fplugin-opt=KindDefaults.Plugin:debug #-}
-- Plugin:
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RoleAnnotations #-}
--Test
{-# LANGUAGE TypeApplications #-}
module Main where

import KindDefaults.Plugin (Defaultable, Promoteable, Collapsible, Ignoreable)

data Label = L | H deriving (Show)

data instance Collapsible Label
type instance Defaultable Label = L

newtype F (l :: Label) a = MkF {unF :: a} deriving (Show)

type instance Promoteable (F _ _) = MkF

class Less (l :: Label) (l' :: Label) where
instance Less L H where
instance Less l l where

data instance Ignoreable (Less H L)

type family Max (l :: Label) (l2 :: Label) where
    Max H _ = H 
    Max _ H = H
    Max _ _ = L

f :: Less H a => F a b -> F H b
f = MkF . unF

f2 :: Max l1 l2 ~ H => F l1 a -> F l2 a
f2 = MkF . unF

main :: IO ()
main = do print "hello"
          print (f (MkF True))
          print (f2 (MkF False))
          print (True :: F H Bool)
          print (True :: F L Bool)
