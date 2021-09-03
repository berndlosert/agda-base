{-# OPTIONS --type-in-type #-}

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
    a : Set

-------------------------------------------------------------------------------
-- Down
-------------------------------------------------------------------------------

record Down (a : Set) : Set where
  constructor Down:
  field getDown : a

open Down public

instance
  Eq-Down : {{Eq a}} -> Eq (Down a)
  Eq-Down ._==_ = equating getDown

  Ord-Down : {{Ord a}} -> Ord (Down a)
  Ord-Down .compare = flip (comparing getDown)
