{-# OPTIONS_GHC -fplugin WRIT.Plugin
                -fplugin-opt=WRIT.Plugin:debug
                -dcore-lint #-}
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

instance Less Public Private
instance Less l l

type family (Max (l :: Label) (l2 :: Label)) :: Label where
    Max Private _ = Private
    Max _ l = l

combine :: lo ~ Max la lb => Box la Int -> Box lb Int -> Box lo Int
combine (Box a) (Box b) = Box (a * b)

salt :: Box Public Int
salt = Box 2

pass :: Box Private Int
pass = Box 42

hash_1 :: Box Private Int
hash_1 = combine pass salt

main1 :: IO ()
main1 = print hash_1

hash_2 :: Box Public Int
hash_2 = combine pass salt



{--
type instance Discharge (Public :: Label) (Private :: Label) =
    Msg (Text "Forbidden flow from public to private"
    :<>: Text " from allowing discharge!")
--}


















hash_3 :: Box Private Int
hash_3 = (pass :: Int) * (salt :: Int)





{--
type instance Promote a (Box l a) =
     Msg (Text "Automatic promotion of unlabeled '"
    :<>: ShowType a :<>: Text "' to a " :<>: ShowType l
    :<>: Text " '" :<>: ShowType a :<>: Text "'!")

type instance Promote (Box _ Int) Int =
     Msg (Text "Automatic unboxing of boxed '"
    :<>: ShowType Int :<>: Text "'!")
--}











hash_4 :: Box label Int
hash_4 = combine pass salt





{--
type instance Default Label = Public
--}


















ensurePrivate_1 :: Less Private l => Box l a -> Box Private a
ensurePrivate_1 (Box a) = Box a


privHash :: Box Private Int
privHash = ensurePrivate_1 hash
  where hash :: Box Private Int
        hash = hash

nonPrivHash :: Box Private Int
nonPrivHash = ensurePrivate_1 pubHash
  where pubHash :: Box Public Int
        pubHash = hash_2

{--
type instance Ignore (Less n m) =
    Msg (Text "Forbidden flow from"
    :<>: Text " ignoring Less!")
--}









ensurePrivate_2 :: Less Private l => Box l a -> Box Private a
ensurePrivate_2 = id


























main :: IO ()
main = do
     print $ hash_1
     print $ hash_2
     print $ hash_3
     print $ hash_4
     print $ ensurePrivate_1 hash_1
     print $ ensurePrivate_2 hash_3
     print $ ensurePrivate_1 hash_2
     print $ ensurePrivate_1 hash_4
     print "done!"























