{-# OPTIONS_GHC -fplugin KindDefaults.Plugin -fplugin-opt=KindDefaults.Plugin:debug #-}
-- Plugin:
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
--{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TemplateHaskell #-}
--Test
{-# LANGUAGE TypeApplications #-}
module Main where

import KindDefaults (Default)

data Label = L
           | H 
           deriving (Show)

type instance Default Label = L

data F (a :: Label) = F deriving (Show)

class Less (l :: Label) (l' :: Label) where
instance Less L H where
instance Less l l where

f :: Less H a => F a -> F H
f F = F

main :: IO ()
main = do print "hello"
          print (f F)
