{-# OPTIONS_GHC -fplugin GRIT.Plugin
                -fplugin-opt=GRIT.Plugin:debug
                -dcore-lint #-}
-- Plugin:
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeOperators #-}
module Main (main) where


import GRIT.Configure

data Label = L | H deriving (Show)

-- By giving the kind Label a Default instance, any ambiguous type variables
-- oft the kind Label will be defaulted to L
type instance Default Label = H

-- You can also give the kind the Relate instance, which allows equality
-- between two of the types. You can either specify the types to match
-- directly (e.g. Relate Label L H), or use variables. If you use the variables,
-- you can further compute to e.g. pretty print the labels.
type instance Relate (n :: Label) (m :: Label) =
    TypeError (Text "Forbidden flow from " :<>: LabelPpr (Max n m)
               :<>: Text " to " :<>: LabelPpr (Min n m) :<>: Text "!")

type family LabelPpr (k :: Label) where
    LabelPpr L = Text "Public"
    LabelPpr H = Text "Secret"
    LabelPpr l = Text "Labeled " :<>: ShowType l


-- Giving the constraint (Less H L) an ignoreable instance simply means that
-- whenever a (Less H L) constraint can't be solved, that is ignored.
type instance Ignore (Less n m) =
    TypeError (Text "Forbidden flow from " :<>: LabelPpr (Max n m)
              :<>: Text " to " :<>: LabelPpr (Min n m) :<>: Text "!")

-- Promotable (F H _) will change any (a ~ F H b) into Coercible a (F H b), but
-- only when the label is H. Can also be written as (F _ _), if it should apply
-- to all labels.
type instance Promote a (F H b) =
     TypeError (Text "Automatic promotion of unlabeled '"
                :<>: ShowType a :<>: Text "' to a Secret '"
                :<>: ShowType b :<>: Text "'!"
                :$$: Text "Perhaps you intended to use 'box'?")
type instance Promote a (F L b) =
     (TypeError (Text "Automatic promotion of unlabeled '"
                 :<>: ShowType a :<>: Text "' to a Public '"
                 :<>: ShowType b :<>: Text "'!"
                 :$$: Text "Perhaps you intended to use 'box'?"))

newtype F (l :: Label) a = MkF {unF :: a} deriving (Show)

box :: a -> F l a
box = MkF

class Less (l :: Label) (l' :: Label) where
instance Less L H where
instance Less l l where

newtype Age = MkAge Int deriving (Show)

type family (Max (l :: Label) (l2 :: Label)) ::Label where
    Max H _ = H
    Max _ l = l

type family Min (l :: Label) (l2 :: Label) where
    Min L _ = L
    Min _ l = l

f :: Less H a => F a b -> F H b
f = MkF . unF

fa :: Less L H => F a b -> F H b
fa = MkF . unF

f2 :: Max l1 l2 ~ H => F l1 a -> F l2 a
f2 = MkF . unF

f3 :: H ~ L => F l1 a -> F l2 a
f3 = MkF . unF

f4 :: Less H L => F a b -> F a b
f4 = MkF . unF

main :: IO ()
main = do print "hello!"
          -- We can solve (Less H a) by defaulting a ~ L, and then solving
          -- Less H L by ignoring it.
          print (f (MkF True))
          print (fa (MkF True))
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
        --   If you have an unspecified type variable that can be defaulted, you
        --   can also promote.
          print ((1 :: Int) :: F l Age)
          let labeledMaybe :: F l (Maybe Bool)
              labeledMaybe = Just True
          print labeledMaybe
          -- Since we're automatically promoting, we can even pattern match on
          -- labeled values.
          case labeledMaybe of
            Just True -> print "Was just true"
            _ -> print "was something else"

