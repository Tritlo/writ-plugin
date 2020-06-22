The WRIT Plugin
======
Weak Runtime-Irrelevant Typing
--------------------------------------------------------------------

A type-checker plugin that allows users to "defaulting" a data kind to a value,
whenever that variable is ambiguous. Also allows automatic promotion to
representationally equal types, as well as ignoring certain constraints, all
parametrized by type families. By default these only improve the error messages
that GHC generates. However, when the `defer` flag is set, any such errors are
converted into warnings, and if integrated with something likeghcide, you can
even see the generated warnings inline in your editor:

![A display of WRIT running with GHCIDE](.github/images/ghcide.png?raw=True "ghcide")

Example:

```haskell
{-# OPTIONS_GHC -fplugin WRIT.Plugin -dcore-lint #-}
-- Plugin:
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RoleAnnotations #-}
module Main (main) where

import WRIT.Configure

import GHC.TypeLits
import Data.Proxy

data Length = AtLeast Nat | Unknown

-- In this library, we know that it is always safe to default an ambiguous type
-- variable of kind Length to Unknown
type instance Default Length = Unknown

-- Then we define length indexed vectors in the following way:
newtype Vec (n :: Length) a = Vec [a] deriving (Show)
type role Vec nominal nominal

-- We also know that is it safe to treat list as vectors with an unknown length.
type instance Promote [a] (Vec Unknown a) =
     (Msg (Text "Automatic promotion of '"
           :<>: ShowType [a] :<>: Text "' to a '"
           :<>: ShowType (Vec Unknown a) :<>: Text "'!"))

type instance Promote (Vec l a) [a] =
     (Msg (Text "Automatic promotion of '"
           :<>: ShowType (Vec l a) :<>: Text "' to a '"
           :<>: ShowType [a] :<>: Text "'!"))

-- Now we can define a safe head function, that only works if we know the length
-- of the list, and the length is at least one.
safeHead :: (length ~ AtLeast n, 1 <= n) => Vec length a -> a
safeHead (Vec (a:_)) = a

type family Dec (k :: Length) :: Length where
    Dec Unknown = Unknown
    Dec (AtLeast 0) = Unknown
    Dec (AtLeast n) = AtLeast (n-1)

safeTail :: (length ~ AtLeast n, 1 <= n) => Vec length a -> Vec (Dec length) a
safeTail (Vec (a:as)) = Vec as

nil :: Vec (AtLeast 0) a
nil = Vec []

type family Inc (k :: Length) :: Length where
    Inc (AtLeast n) = AtLeast (n+1)
    Inc Unknown = AtLeast 1

(>:) :: a -> Vec length a -> Vec (Inc length) a
a>:(Vec as) = Vec (a:as)
infixr 3 >:

type family Add (l1 :: Length) (l2 :: Length) :: Length where
    Add (AtLeast n) (AtLeast m) = AtLeast (n+m)
    Add Unknown (AtLeast m) = AtLeast m
    Add (AtLeast n) Unknown = AtLeast n
    Add _ _ = Unknown

toVec :: Vec length a -> [a]
toVec (Vec as) = as

fromList :: [a] -> Vec Unknown a
fromList as = Vec as

(+:+) :: Vec l1 a -> Vec l2 a -> Vec (Add l1 l2) a
(+:+) (Vec a) (Vec b) = Vec (a ++ b)

fromKnownList :: forall n a. KnownNat n => [a] -> Vec (AtLeast n) a
fromKnownList as =
     if length as == fromIntegral (natVal (Proxy @n))
     then Vec as
     else error "fromKnownList: Length of list does not match proof!"

knownVec :: Vec (AtLeast 3) Int
knownVec = fromKnownList [1,2,3]

vmap :: (a -> b) -> Vec l a -> Vec l b
vmap = map


class (l :: Length) >= (n :: Nat) where

safe2H :: length >= 2 => Vec length a -> (a,a)
safe2H (Vec (a:b:_)) = (a,b)

type instance Ignore (AtLeast n >= m) =
  OnlyIf (m <= n) (Msg (Text "AtLeast " :<>: ShowType m
                        :<>: Text " is at least "
                        :<>: ShowType n))

forget :: Vec l a -> Vec Unknown a
forget a = a

main :: IO ()
main = do print "Enter a list of numbers!"
          -- Note that this is almost like deriving Read (Vec Unknown a) via Read a
          xs <- read @[Int]  <$> return "[1,3,5]" -- getLine
          print $ safeHead ((7 :: Int)>:xs)
          print $ safeTail ((2 :: Int)>:xs)
          let k = ((2 :: Int)>:xs)
              mk = map (+ (1:: Int)) k
          print mk
          print (vmap (+1) k)
          -- Does not compile, since the length of xs is unknown
          -- print $ safeTail $ safeTail (2>:xs)
          -- Pattern matching works if we can promote to any length,
          -- but not if we only promote to Unknown
          let n1 = True>:nil
              n2 = True>:False>:nil
              n4 = True>:True>:False>:False>:nil
          print (safe2H n2)
          print (safe2H n4)
          -- Note that since we can only promote to Vec Unknown, we must forget
          -- in order to case match.
          case forget n2 of
            [True, False] -> print "matched!"
            _ -> print "didn't match"
          -- These won't compile
          -- print (safeHead (nil @Int))
          -- print (safeHead ([] @Int))
```

This will output:

```console
Build profile: -w ghc-8.8.3 -O1
In order, the following will be built (use -v for more details):
 - TestVec-1.0.0 (exe:test_vec) (file Test.hs changed)
Preprocessing executable 'test_vec' for TestVec-1.0.0..
Building executable 'test_vec' for TestVec-1.0.0..
[1 of 1] Compiling Main             ( Test.hs, /home/tritlo/writ-plugin/dist-newstyle/build/x86_64-linux/ghc-8.8.3/TestVec-1.0.0/x/test_vec/build/test_vec/test_vec-tmp/Main.o )
Test.hs:93:8: warning:
    Defaulting ‘l :: Length’ to ‘'Unknown’ in ‘[b] ~ Vec l b’
   |
93 | vmap = map
   |        ^^^

Test.hs:93:8: warning:
    Automatic promotion of '[b]' to a 'Vec 'Unknown b'!
   |
93 | vmap = map
   |        ^^^

Test.hs:107:12: warning:
    Defaulting ‘l :: Length’ to ‘'Unknown’ in ‘l ~ 'Unknown’
    |
107 | forget a = a
    |            ^

Test.hs:113:29: warning:
    Defaulting ‘length0 :: Length’ to ‘'Unknown’ in
    ‘Inc length0 ~ 'AtLeast n0’
    |
113 |           print $ safeHead ((7 :: Int)>:xs)
    |                             ^^^^^^^^^^^^^^

Test.hs:113:41: warning:
    Defaulting ‘length0 :: Length’ to ‘'Unknown’ in
    ‘[Int] ~ Vec length0 Int’
    |
113 |           print $ safeHead ((7 :: Int)>:xs)
    |                                         ^^

Test.hs:113:41: warning:
    Automatic promotion of '[Int]' to a 'Vec 'Unknown Int'!
    |
113 |           print $ safeHead ((7 :: Int)>:xs)
    |                                         ^^

Test.hs:114:29: warning:
    Defaulting ‘length0 :: Length’ to ‘'Unknown’ in
    ‘Inc length0 ~ 'AtLeast n0’
    |
114 |           print $ safeTail ((2 :: Int)>:xs)
    |                             ^^^^^^^^^^^^^^

Test.hs:114:41: warning:
    Defaulting ‘length0 :: Length’ to ‘'Unknown’ in
    ‘[Int] ~ Vec length0 Int’
    |
114 |           print $ safeTail ((2 :: Int)>:xs)
    |                                         ^^

Test.hs:114:41: warning:
    Automatic promotion of '[Int]' to a 'Vec 'Unknown Int'!
    |
114 |           print $ safeTail ((2 :: Int)>:xs)
    |                                         ^^

Test.hs:115:32: warning:
    Defaulting ‘length0 :: Length’ to ‘'Unknown’ in
    ‘[Int] ~ Vec length0 Int’
    |
115 |           let k = ((2 :: Int)>:xs)
    |                                ^^

Test.hs:115:32: warning:
    Automatic promotion of '[Int]' to a 'Vec 'Unknown Int'!
    |
115 |           let k = ((2 :: Int)>:xs)
    |                                ^^

Test.hs:116:38: warning:
    Defaulting ‘length0 :: Length’ to ‘'Unknown’ in
    ‘Vec (Inc length0) Int ~ [Int]’
    |
116 |               mk = map (+ (1:: Int)) k
    |                                      ^

Test.hs:116:38: warning:
    Automatic promotion of 'Vec ('AtLeast 1) Int' to a '[Int]'!
    |
116 |               mk = map (+ (1:: Int)) k
    |                                      ^

Test.hs:126:18: warning: AtLeast 2 is at least 2
    |
126 |           print (safe2H n2)
    |                  ^^^^^^^^^

Test.hs:127:18: warning: AtLeast 2 is at least 4
    |
127 |           print (safe2H n4)
    |                  ^^^^^^^^^

Test.hs:131:13: warning:
    Automatic promotion of '[Bool]' to a 'Vec 'Unknown Bool'!
    |
131 |             [True, False] -> print "matched!"
    |             ^^^^^^^^^^^^^
Linking /home/tritlo/writ-plugin/dist-newstyle/build/x86_64-linux/ghc-8.8.3/TestVec-1.0.0/x/test_vec/build/test_vec/test_vec ...
"Enter a list of numbers!"
7
Vec [1,3,5]
[3,2,4,6]
Vec [3,2,4,6]
(True,False)
(True,True)
"matched!"
```

I.e. all the would be errors are turned into warnings, and the code compiles and
runs, with the correct core being generated (as verified by `-dcore-lint`).
