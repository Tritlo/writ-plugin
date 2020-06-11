The SACRED Plugin
======
Somewhat Automatic Coercion of Representationally Equivalent Domains
--------------------------------------------------------------------

A type-checker plugin that allows users to "defaulting" a data kind to a value,
whenever that variable is ambiguous. Also allows automatic promotion to
representationally equal types, as well as ignoring certain constraints.
All parametrized by type families.

Example:

```haskell
{-# OPTIONS_GHC -fplugin KindDefaults.Plugin
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

import KindDefaults.Plugin (Default, Promote, Ignore, Relate)
import GHC.TypeLits (TypeError(..),ErrorMessage(..))

data Label = L | H deriving (Show)

-- By giving the kind Label a Default instance, any ambiguous type variables
-- oft the kind Label will be defaulted to L
type instance Default Label = L

-- You can also give the kind the Relate instance, which allows equality
-- between two of the types. You can either specify the types to match
-- directly (e.g. Relate Label L H), or use variables. If you use the variables,
-- you can further compute to e.g. pretty print the labels.
type instance Relate Label (n :: Label) (m :: Label) =
    TypeError (Text "Forbidden flow from "
                 :<>: LabelPpr (Max n m)
                 :<>: Text " to "
                 :<>: LabelPpr (Min n m)
                 :<>: Text "!")

type family LabelPpr (k :: Label) where
    LabelPpr L = Text "Public (L)"
    LabelPpr H = Text "Secret (H)"

-- Giving the constraint (Less H L) an ignoreable instance simply means that
-- whenever a (Less H L) constraint can't be solved, that is ignored.
type instance Ignore (Less n m) =
    TypeError (Text "Forbidden flow from "
                 :<>: LabelPpr (Max n m)
                 :<>: Text " to "
                 :<>: LabelPpr (Min n m)
                 :<>: Text "!")

newtype F (l :: Label) a = MkF {unF :: a} deriving (Show)

-- Promotable (F H _) will change any (a ~ F H b) into Coercible a (F H b), but
-- only when the label is H. Can also be written as (F _ _), if it should apply
-- to all labels.
type instance Promote a (F H b) =
     TypeError (Text "Automatic promotion of unlabeled '"
                :<>: ShowType a :<>: Text "' to a Secret '" :<>: ShowType b :<>: Text "'!"
                :$$: Text "Perhaps you intended to use 'box'?")
type instance Promote a (F L b) =
     TypeError (Text "Automatic promotion of unlabeled '"
                :<>: ShowType a :<>: Text "' to a Public '" :<>: ShowType b :<>: Text "'!"
                :$$: Text "Perhaps you intended to use 'box'?")

class Less (l :: Label) (l' :: Label) where
instance Less L H where
instance Less l l where

newtype Age = MkAge Int deriving (Show)

type family (Max (l :: Label) (l2 :: Label)) ::Label where
    Max H _ = H 
    Max _ H = H
    Max _ _ = L

type family Min (l :: Label) (l2 :: Label) where
    Min L _ = L
    Min _ l = l

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

```

This will output:

```console
Test.hs:98:18: warning: Defaulting ‘a :: Label’ to ‘L’
   |
98 |           print (f (MkF True))
   |                  ^^^^^^^^^^^^

Test.hs:101:18: warning:
    Forbidden flow from Secret (H) to Public (L)!
    |
101 |           print (f2 (MkF False))
    |                  ^^^^^^^^^^^^^^

Test.hs:101:18: warning: Defaulting ‘l1 :: Label’ to ‘L’
    |
101 |           print (f2 (MkF False))
    |                  ^^^^^^^^^^^^^^

Test.hs:101:18: warning: Defaulting ‘l2 :: Label’ to ‘L’
    |
101 |           print (f2 (MkF False))
    |                  ^^^^^^^^^^^^^^

Test.hs:104:18: warning:
    Forbidden flow from Secret (H) to Public (L)!
    |
104 |           print (f3 (MkF 0))
    |                  ^^^^^^^^^^

Test.hs:107:18: warning:
    Automatic promotion of unlabeled 'Bool' to a Secret 'Bool'!
    Perhaps you intended to use 'box'?
    |
107 |           print (True :: F H Bool)
    |                  ^^^^

Test.hs:108:18: warning:
    Automatic promotion of unlabeled 'Bool' to a Public 'Bool'!
    Perhaps you intended to use 'box'?
    |
108 |           print (True :: F L Bool)
    |                  ^^^^

Test.hs:111:19: warning:
    Automatic promotion of unlabeled 'Int' to a Public 'Age'!
    Perhaps you intended to use 'box'?
    |
111 |           print ((1 :: Int) :: F L Age)
    |                   ^^^^^^^^
Linking /home/tritlo/kind-default-plugin/dist-newstyle/build/x86_64-linux/ghc-8.10.1/Test-1.0.0/x/test/build/test/test ...
"hello"
MkF {unF = True}
MkF {unF = False}
MkF {unF = 0}
MkF {unF = 0}
MkF {unF = True}
MkF {unF = True}
MkF {unF = MkAge 1}
```

I.e. all the would be errors are turned into warnings, and the code still
compiles and runs.