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

-- Discharge means that we are allowed to discharge (a :: k) ~ (b :: k),
-- if c holds.
type family Discharge (a :: k) (b :: k) :: Message

-- An Ignore cons means that we are allowd to ignore the constraint con.
-- Note! This only works for empty classes!
type family Ignore (k :: Constraint) :: Message

-- Promote means that if we have a value (True :: Bool), we can promote it to b
-- Note that Promote a b requires Coercible a b, otherwise a Coercible error
-- will be produced. Note that:
--               type instance Promote a b = m
--                           ===
-- type instance Discharge a b = OnlyIf (Corecible a b) m
type family Promote (a :: *) (b :: *) :: Message

-- We require that Discharge a b is the same as Promote a b.
type instance Discharge (a :: *) (b :: *) =
    OnlyIf (Coercible a b) (Promote a b)

-- OnlyIf can be used to communicate additional constraints on promotions,
-- discharges, and ignores.
type family OnlyIf (c :: Constraint) (m :: Message) :: Message where
  OnlyIf k m = m

-- Report is a class we use to wrap TypeErrors so that any type families
-- within can be computed. It can be used with a TypeError to turn that error
-- into a warning at compile time.
class Report (err :: Message) where
