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

import KindDefaults.Plugin (Defaultable, Promoteable, Collapsible,
                            Ignoreable, Equivable)
import GHC.TypeLits (TypeError(..),ErrorMessage(..))

data Label = L | H deriving (Show)

-- By giving the kind Label a Defaultable instance, any ambiguous type variables
-- oft the kind Label will be defaulted to L
type instance Defaultable Label = L


-- By giving the kind Label a Collapsible instance, we allow L ~ H and H ~ L,
-- but you have to give the user an explanation in the error message.
type instance Collapsible Label =
    TypeError (Text "Forbidden flow from Secret (H) to Public (L)!")

-- You can also give the kind the more limited Equivable instance, which only
-- allows equiality between two of the types, in one direction. I.e. this would
-- allow L ~ H, but not H ~ L. Useful for when you only want some members of a
-- kind to be equivalent, but not others.
type instance Equivable Label L H =
    TypeError (Text "Forbidden flow from Secret (H) to Public (L)!")

-- Giving the constraint (Less H L) an ignoreable instance simply means that
-- whenever a (Less H L) constraint can't be solved, that is ignored.
type instance Ignoreable (Less H L) =
    TypeError (Text "Forbidden flow from Secret (H) to Public (L)!")

newtype F (l :: Label) a = MkF {unF :: a} deriving (Show)

-- Promotable (F H _) will change any (a ~ F H b) into Coercible a (F H b), but
-- only when the label is H. Can also be written as (F _ _), if it should apply
-- to all labels.
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

f3 :: H ~ L => F l1 a -> F l2 a
f3 = MkF . unF

f4 :: Less H L => F a b -> F a b
f4 = MkF . unF


main :: IO ()
main = do print "hello"
          -- We can solve (Less H a) by defaulting a ~ L, and then solving
          -- Less H L by ignoring it.
          print (f (MkF True))
          -- By defaulting l1 and l2 to L, Max l1 l2 becomes L
          -- we then solve this by equivaling L ~ H.
          print (f2 (MkF False))
          -- Here we're asked to solve H ~ L, which we can do by collapsing
          -- Label.
          print (f3 (MkF 0))
          print (f4 (MkF 0))
          -- We can promote automatically, ignoring the labels.
          print (True :: F H Bool)
          print (True :: F L Bool)
          -- Not that we are turning this into a coercion, so that if
          -- Int is coercible to Age, the promotion works.
          print ((1 :: Int) :: F L Age)
