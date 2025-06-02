module Data.Ord.Down where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a : Type

-------------------------------------------------------------------------------
-- Down
-------------------------------------------------------------------------------

record Down (a : Type) : Type where
  constructor down
  field getDown : a

open Down public

instance
  Eq-Down : {{Eq a}} -> Eq (Down a)
  Eq-Down ._==_ x y = getDown x == getDown y

  Ord-Down : {{Ord a}} -> Ord (Down a)
  Ord-Down ._<_ x y = getDown y < getDown x
