{-# OPTIONS_GHC -fplugin KindDefaults.Plugin
                -fplugin-opt=KindDefaults.Plugin:debug
                 #-}
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
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeOperators #-}
--Test
{-# LANGUAGE TypeApplications #-}
module Main where

import KindDefaults.Plugin (Defaultable, Promoteable, Collapsible, Ignoreable)
import GHC.TypeLits (TypeError(..),ErrorMessage(..))

data Label = L | H deriving (Show)
type instance Defaultable Label =
    '(L, TypeError (Text "Defaulting Label to Public (L)!"))

type instance Collapsible Label =
    TypeError (Text "Forbidden flow from Secret (H) to Public (L)!")
type instance Ignoreable (Less H L) =
    TypeError (Text "Forbidden flow from Secret (H) to Public (L)!")

newtype F (l :: Label) a = MkF {unF :: a} deriving (Show)

type instance Promoteable (F H _) =
     TypeError (Text "Automatic promotion of unlabeled value to a Secret value!"
                :$$: Text "Perhaps you intended to use 'box'?")
type instance Promoteable (F L _) =
     TypeError (Text "Automatic promotion of unlabeled value to a Public value!"
                :$$: Text "Perhaps you intended to use 'box'?")

class Less (l :: Label) (l' :: Label) where
instance Less L H where
instance Less l l where


type family Max (l :: Label) (l2 :: Label) where
    Max H _ = H 
    Max _ H = H
    Max _ _ = L

f :: Less H a => F a b -> F H b
f = MkF . unF

f2 :: Max l1 l2 ~ H => F l1 a -> F l2 a
f2 = MkF . unF

f3 :: Less H L => F a b -> F H b
f3 = MkF . unF

f4 :: Less H L => F a b -> F a b
f4 = MkF . unF

main :: IO ()
main = do print "hello"
          print (f (MkF True))
          print (f2 (MkF False))
          print (f3 (MkF 0))
          print (f4 (MkF [10]))
          print (True :: F H Bool)
          print (True :: F L Bool)
