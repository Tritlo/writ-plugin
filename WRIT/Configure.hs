{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
module WRIT.Configure (
        Default, Promote, Ignore, Discharge,
        Message(..), TypeError(..), ErrorMessage(..),
        -- Dynamic extension
        castDyn, dynDispatch, Dispatchable
) where

import GHC.TypeLits (TypeError(..),ErrorMessage(..))
import Data.Kind (Constraint, Type)
import Data.Coerce (Coercible)
import Data.Map

-- castDyn
import Data.Typeable
import Type.Reflection (SomeTypeRep, someTypeRep)
import Data.Dynamic
import GHC.Stack
import Data.Maybe (fromJust)

-- We use the Message to reflect that these can also appear
-- in warnings when using GRIT, and the same with Msg for TypeError.
data {-kind-} Message
  = Msg ErrorMessage -- ^ Msg holds an ErrorMessage that  will be output as part
                     -- of applying a rule, either as a warning or as a type
                     -- error if the keep-errors flag is set.
  | OnlyIf Constraint Message -- ^ OnlyIfs are messages which contain additional
                              -- constraints, and specify to the plugin that an
                              -- additional constraint must be checked when
                              -- applying a given rule.

-- | The Default family allows us to 'default' free type variables of a given
-- kind in a constraint to the given value, i.e. if there is an instance
-- Default k for and a is a free type variable of kind k in constraint c,
-- then a ~ Default k will be added to the context of c, and
-- Γ, a ~ Defaul k |- c : Constraint checked for validity.
type family Default k :: k

-- | The Ignore family allows us to 'ignore' a given constraint.  Ignore C means
-- that we can discharge the constraint C whenever it is encountered, however,
-- this is only allowed when the constraint C is an empty class dictionary.
type family Ignore (c :: Constraint) :: Message

-- | The Discharge family allows us to specify equalities that can be discharged.
-- Note that Discharge is a special case of ignore for primitive equality
-- constraints, i.e. (a :: k) ~# (b :: k). But since primitive equality is not
-- specifiable as a matchable constraint for ignore, since the user defined
-- uses the ~ operator.
type family Discharge (a :: k) (b :: k) :: Message

-- | The Promote family is a special case of the Discharge family that allows us
-- to specify which values can be automatically promoted to other values, if
-- they are Coercible.
type family Promote (a :: Type) (b :: Type) :: Message

-- We require that Discharge (a :: *) (b :: *) to be Promote a b for any a,b.
type instance Discharge (a :: Type) (b :: Type) =
   OnlyIf (Coercible a b) (Promote a b)


-- | castDyn casts a Dynamic to any typeable value, and fails with a descriptive
-- error if the types dont match. Automatically inserted for casting Dynamic
-- values back to static values.
castDyn :: forall a . (Typeable a, HasCallStack) => Dynamic -> a
castDyn arg = fromDyn arg err
  where err = error ("Couldn't match expected type '" ++ target
                     ++ "' with actual dynamic type '" ++ actual  ++ "'")
        target = show (someTypeRep (Proxy :: Proxy a))
        actual = show (dynTypeRep arg)

class Dispatchable (c :: Type -> Constraint) where

dynDispatch :: forall a b . (Typeable a, Typeable b)
            => Map (String, SomeTypeRep) Dynamic -- ^ Provided by the plugin
            -> String                            -- ^ The name of the function
            -> a -> b
dynDispatch insts fun_name a =
    case insts !? (fun_name, argt) of
      Just f ->
         let res = dynApp f $ toDyn a
         in fromDyn res
         (error $ "Incorrect types! Applying '"
         ++ fun_name ++ " :: "
         ++ show (dynTypeRep f)
         ++ "' to '" ++ show argt
         ++ " expecting '" ++ show targett
         ++"' but got '" ++ show (dynTypeRep res) ++ "'")
      _ -> error $ "Instance of '"
                  ++ fun_name ++ " :: " ++ show argt ++ " -> " ++ show targett
                  ++ "' not found in dispatch table!"
 where argt = typeOf a
       targett = someTypeRep (Proxy :: Proxy b)