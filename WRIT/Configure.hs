{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
module WRIT.Configure (
        Default, TypeError(..), ErrorMessage(..),
        -- Dynamic extension
        castDyn, dynDispatch
) where

import GHC.TypeLits (TypeError(..),ErrorMessage(..))
import Data.Kind (Constraint, Type)
import Data.Coerce (Coercible)

-- castDyn
import Data.Typeable
import Type.Reflection (SomeTypeRep, someTypeRep)
import Data.Dynamic
import GHC.Stack
import Data.Maybe (fromJust)

-- | The Default family allows us to 'default' free type variables of a given
-- kind in a constraint to the given value, i.e. if there is an instance
-- Default k for and a is a free type variable of kind k in constraint c,
-- then a ~ Default k will be added to the context of c, and
-- Γ, a ~ Defaul k |- c : Constraint checked for validity.
type family Default k :: k

-- | castDyn casts a Dynamic to any typeable value, and fails with a descriptive
-- error if the types dont match. Automatically inserted for casting Dynamic
-- values back to static values.
castDyn :: forall a . (Typeable a, HasCallStack) => Dynamic -> a
castDyn arg = fromDyn arg err
  where err = error ("Couldn't match expected type '" ++ target
                     ++ "' with actual dynamic type '" ++ actual  ++ "'")
        target = show (someTypeRep (Proxy :: Proxy a))
        actual = show (dynTypeRep arg)

dynDispatch :: forall b . (Typeable b)
            => [(SomeTypeRep, Dynamic)] -- ^ Provided by the plugin
            -> String                   -- ^ The name of the function
            -> String                   -- ^ The name of the class
            -> Dynamic -> b
dynDispatch insts fun_name class_name dispatcher =
    case lookup argt insts of
      Just f ->
         fromDyn f
         (error $ "Type mismatch when dispatching '"
         ++ fun_name
         ++ "' expecting '" ++ show targett
         ++"' but got '" ++ show (dynTypeRep f)
         ++ "' using dispatch table for '"
         ++ class_name ++ "'!")
      _ -> error $ "No instance of '" ++ class_name ++ " " ++ show argt ++ "'"
                  ++ " found when dispatching for '"
                  ++ fun_name ++ " :: " ++ show argt ++ " -> " ++ show targett
                  ++ "'."
 where argt = dynTypeRep dispatcher
       targett = someTypeRep (Proxy :: Proxy b)
