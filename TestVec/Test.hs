{-# OPTIONS_GHC -fplugin GRIT.Plugin -dcore-lint
                -fplugin-opt=GRIT.Plugin:debug
 #-}
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
{-# LANGUAGE Safe #-}
module Main (main) where

import GRIT.Configure

import GHC.TypeLits
import Data.Proxy

data Length = AtLeast Nat | Unknown

-- In this library, we know that it is always safe to default an ambiguous type
-- variable of kind Length to Unknown
type instance Default Length = Unknown

-- Then we define length indexed vectors in the following way:
newtype Vec (n :: Length) a = Vec [a] deriving (Show)

class IsUnknownOrZero (length :: Length)

instance IsUnknownOrZero Unknown where

instance IsUnknownOrZero (AtLeast 0) where

instance
  (Report (TypeError (
         Text "Cannot safely promote a list to a 'Vec length' unless the"
         :$$: Text "desired length is 0 or Unknown, but here the length is "
         :<>: ShowType n :<>: Text ".")), 1 <= n) =>
   IsUnknownOrZero (AtLeast n) where

type instance Discharge Unknown (n :: Length) =
    OnlyIf (n ~ AtLeast 0) (TypeError (Text "All unknowns lengths are at least 0"))

-- We also know that is it safe to treat list as vectors with an unknown length.
type instance Promote [a] (Vec length a) =
    OnlyIf (IsUnknownOrZero length)
     (TypeError (Text "Automatic promotion of '"
                 :<>: ShowType [a] :<>: Text "' to a '"
                 :<>: ShowType (Vec Unknown a) :<>: Text "'!"))

type instance Promote (Vec l a) [a] =
     (TypeError (Text "Automatic promotion of '"
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

main :: IO ()
main = do print "Enter a list of numbers!"
          -- Note that this is almost like deriving Read (Vec Unknown a) via Read a
          xs <- read @[Integer]  <$> return "[1,3,5]" -- getLine
          print $ safeHead (7>:xs)
          print $ safeTail (2>:xs)
          let k = (2>:xs)
              mk = map (+1) k
          print mk
          print (vmap (+1) k)
          -- Does not compile, since the length of xs is unknown
          -- print $ safeTail $ safeTail (2>:xs)
          -- Pattern matching works if we can promote to any length,
          -- but not if we only promote to Unknown
          case (2>:xs) of
              (2:[]) -> print "Rest was empty"
              _ -> print "Rest was something else"


