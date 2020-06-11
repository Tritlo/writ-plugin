{-# OPTIONS_GHC -fplugin KindDefaults.Plugin
                -fplugin-opt=KindDefaults.Plugin:debug
                -fplugin-opt=KindDefaults.Plugin:defer
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

type instance Defaultable Label = L

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

newtype Age = MkAge Int deriving (Show)

type family Max (l :: Label) (l2 :: Label) where
    Max H _ = H 
    Max _ H = H
    Max _ _ = L

f :: Less H a => F a b -> F H b
f = MkF . unF

f2 :: Max l1 l2 ~ H => F l1 a -> F l2 a
f2 = MkF . unF

f3 :: Less H L => F a b -> F a b
f3 = MkF . unF

main :: IO ()
main = do print "hello"
          -- We can solve (Less H a) by defaulting a ~ L, and then solving
          -- Less H L by ignoring it.
          print (f (MkF True))
          -- By defaulting l1 and l2 to L, Max l1 l2 becomes L
          -- we then solve this by collapsing L ~ H.
          print (f2 (MkF False))
          print (f3 (MkF 0))
          -- We can promote automatically, ignoring the labels.
          print (True :: F H Bool)
          print (True :: F L Bool)
          -- Not that we are turning this into a coercion, so that if
          -- Int is coercible to Age, the promotion works.
          print ((1 :: Int) :: F L Age)
