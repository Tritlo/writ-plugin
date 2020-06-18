{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeFamilies #-}
module GRIT.Configure (
        Default, Promote, Ignore, Relate,
        TypeError(..), ErrorMessage(..), Message
) where

import GHC.TypeLits (TypeError(..),ErrorMessage(..))

import GHC.TypeLits (ErrorMessage)
import Data.Kind (Constraint)

-- We give ErrorMessage a new name to reflect that they can also appear in
-- warnings when using GRIT
type Message = ErrorMessage

-- Default means that if we have an ambiguous l1 of kind k, we can default it to
-- be the rhs, i.e. type family Default Label = L would default all
-- ambiguous type variables of kind Label to L
type family Default k :: k

-- Promote means that if we have a value (True :: Bool), we can promote it to (k Bool)
-- Note that Promote a k requires Coercible a k, otherwise a Coercible error  will be produced.
type family Promote (a :: *) (k :: *) :: Message

-- An Ignore cons means that we are allowd to ignore the constraint con.
-- Note! This only works for empty classes!
type family Ignore (k :: Constraint) :: Message

-- Relate means that we are allowed to discharge (a :: k) ~ (b :: k)
type family Relate k (a :: k) (b :: k) :: Message

-- Report is a class we use to wrap TypeErrors so that any type families
-- within can be computed. It's closed, so we know that the only instances of
-- Report will be the ones we generated.
class Report (err :: Message) where
