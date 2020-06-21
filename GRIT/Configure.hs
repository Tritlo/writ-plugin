{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
module GRIT.Configure (
        Default, Promote, Ignore, Discharge,
        Report, Message, Msg, OnlyIf,
        TypeError(..), ErrorMessage(..),
) where

import GHC.TypeLits (TypeError(..),ErrorMessage(..))
import Data.Kind (Constraint)
import Data.Coerce (Coercible)

-- We give the new name Message to reflect that these can also appear
-- in warnings when using GRIT, and the same with Msg for TypeError.
type Message = ErrorMessage

type family Msg (m :: Message) :: Message where
  Msg m = TypeError m


-- Default means that if we have an ambiguous l1 of kind k, we can default it to
-- be the rhs, i.e. type family Default Label = L would default all
-- ambiguous type variables of kind Label to L
type family Default k :: k

-- We define an instance for (*) here to trigger overlap errors, since
-- defaulting for (*) might be unsound.
type instance Default (*) = ()

-- Ignore c means that we can ignore the constraint c. Note! We only ignore
-- runtime-irrelevant classes, i.e. classes with no methods.
type family Ignore (c :: Constraint) :: Message

-- Discharge a b = m means that we are allowed to discharge (a :: k) ~ (b :: k),
-- if m holds.
type family Discharge (a :: k) (b :: k) :: Message


-- Promote means that if we have a value (True :: Bool), we can promote it to b
-- Note that Promote a b requires Coercible a b, otherwise a Coercible error
-- will be produced.
type family Promote (a :: *) (b :: *) :: Message

-- We require that Discharge (a :: *) (b :: *) to be Promote a b for any a,b.
type instance Discharge (a :: *) (b :: *) =
    OnlyIf (Coercible a b) (Promote a b)

-- OnlyIf can be used to communicate additional constraints on promotions,
-- discharges, and ignores.
type family OnlyIf (c :: Constraint) (m :: Message) :: Message where
  OnlyIf k m = m

-- Report is a class we use to wrap messages so that they can either be returned
-- as a type error or reported as a warning (after any type families within have
-- been computed).
class Report (err :: Message) where
