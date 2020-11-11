{-# OPTIONS_GHC -fplugin WRIT.Plugin
                -fplugin-opt=WRIT.Plugin:debug
                -dcore-lint #-}
-- Plugin:
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
module Main (main) where

import WRIT.Configure

data Label = Public | Private deriving (Show)

newtype Box (l :: Label) a = Box {unBox :: a} deriving (Show)

class Less (l :: Label) (l' :: Label)

instance Less Public Private where
instance Less l l where

type family (Max (l :: Label) (l2 :: Label)) :: Label where
    Max Private _ = Private
    Max _ l = l

type instance Discharge (Public :: Label) (Private :: Label) =
    Msg (Text "Forbidden flow from public to private"
    :<>: Text " from allowing discharge!")

type instance Promote a (Box l a) =
     Msg (Text "Automatic promotion of unlabeled '"
    :<>: ShowType a :<>: Text "' to a " :<>: ShowType l
    :<>: Text " '" :<>: ShowType a :<>: Text "'!")

type instance Promote (Box _ Int) Int =
     Msg (Text "Automatic unboxing of boxed '"
    :<>: ShowType Int :<>: Text "'!")

type instance Default Label = Public

type instance Ignore (Less n m) =
    Msg (Text "Forbidden flow from"
    :<>: Text " ignoring Less!")

main :: IO ()
main =
  do let -- Combine is our (naive) salting function
         combine :: lo ~ Max la lb => Box la Int
                 -> Box lb Int -> Box lo Int
         combine (Box a) (Box b) = Box (a * b)

         -- Here's a function that allows us to assert privacy
         ensurePrivate_1 :: Less Private l => Box l a -> Box Private a
         ensurePrivate_1 (Box a) = Box a

         pass :: Box Public Int
         pass = Box 2
         salt :: Box Private Int
         salt = Box 42

         -- Hash 1 works, because we're not breaking any rules
         hash_1 :: Box Private Int
         hash_1 = combine pass salt

        --  We got the label wrong, but it's OK, since we have Discharge
         hash_2 :: Box Public Int
         hash_2 = combine pass salt

         -- If we don't want to write a function just yet, but we can
         -- Promote to a box and then Promote again to unbox.
         hash_3 :: Box Private Int
         hash_3 = (pass :: Int) * (salt :: Int)

         -- We don't even have to pick a label, since we can default.
         hash_4 :: Box label Int
         hash_4 = combine pass salt

        -- Similarly, we can have discharge and default "lift" id to
        -- be the ensurePrivate function:
         ensurePrivate_2 :: Less Private l => Box l a -> Box Private a
         ensurePrivate_2 = id

         -- Here, id is turned from a -> a to Box l a -> Box l a during
         -- typechecking. Then, the l is Defaulted to be Public, and
         -- matched with a check of Public ~ Private, which is Discharged.

     print $ ensurePrivate_1 hash_1
     print $ ensurePrivate_1 hash_2
     print $ ensurePrivate_2 hash_2
     print "done!"