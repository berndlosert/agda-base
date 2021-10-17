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
  constructor aDown
  field getDown : a

open Down public

instance
  Eq-Down : {{Eq a}} -> Eq (Down a)
  Eq-Down ._==_ = _==_ on getDown

  Ord-Down : {{Ord a}} -> Ord (Down a)
  Ord-Down ._<_ = _>_ on getDown
