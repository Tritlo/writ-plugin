KindDefaults
============

A type-checker plugin that allows users to "defaulting" a data kind to a value,
whenever that variable is ambiguous. Also allows automatic promotion to
representationally equal types, as well as ignoring certain constraints.
All parametrized by type families.

Example:

```haskell
{-# OPTIONS_GHC -fplugin KindDefaults.Plugin
                -fplugin-opt=KindDefaults.Plugin:defer #-}
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

-- By giving the kind Label a Defaultable instance, any ambiguous type variables
-- oft the kind Label will be defaulted to L
type instance Defaultable Label = L


-- By giving the kind Label a Collapsible instance, we allow L ~ H and H ~ L,
-- but you have to give the user an explanation in the error message.
type instance Collapsible Label =
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
```

This will output:

```console
Test.hs:77:18: warning: Defaulting: a0 ~ 'L
   |
77 |           print (f (MkF True))
   |                  ^^^^^^^^^^^^

Test.hs:77:18: warning:
    Ignoring: Forbidden flow from Secret (H) to Public (L)!
   |
77 |           print (f (MkF True))
   |                  ^^^^^^^^^^^^

Test.hs:80:18: warning: Defaulting: l10 ~ 'L
   |
80 |           print (f2 (MkF False))
   |                  ^^^^^^^^^^^^^^

Test.hs:80:18: warning: Defaulting: l20 ~ 'L
   |
80 |           print (f2 (MkF False))
   |                  ^^^^^^^^^^^^^^

Test.hs:80:18: warning:
    Collapsing: Forbidden flow from Secret (H) to Public (L)!
   |
80 |           print (f2 (MkF False))
   |                  ^^^^^^^^^^^^^^

Test.hs:81:18: warning:
    Ignoring: Forbidden flow from Secret (H) to Public (L)!
   |
81 |           print (f3 (MkF 0))
   |                  ^^^^^^^^^^

Test.hs:83:18: warning:
    Promoting: Automatic promotion of unlabeled value to a Secret value!
               Perhaps you intended to use 'box'?
   |
83 |           print (True :: F H Bool)
   |                  ^^^^

Test.hs:84:18: warning:
    Promoting: Automatic promotion of unlabeled value to a Public value!
               Perhaps you intended to use 'box'?
   |
84 |           print (True :: F L Bool)
   |                  ^^^^

Test.hs:87:19: warning:
    Promoting: Automatic promotion of unlabeled value to a Public value!
               Perhaps you intended to use 'box'?
   |
87 |           print ((1 :: Int) :: F L Age)
   |                   ^^^^^^^^
Linking /home/tritlo/kind-default-plugin/dist-newstyle/build/x86_64-linux/ghc-8.10.1/Test-1.0.0/x/test/build/test/test ...
"hello"
MkF {unF = True}
MkF {unF = False}
MkF {unF = 0}
MkF {unF = True}
MkF {unF = True}
MkF {unF = MkAge 1}
```

I.e. all the would be errors are turned into warnings, and the code still
compiles and runs.