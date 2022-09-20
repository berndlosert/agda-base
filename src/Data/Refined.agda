module Data.Refined where

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
-- Refined
-------------------------------------------------------------------------------

data Refined (a : Set) (p : a -> Bool) : Set where
  unsafeRefine : a -> Refined a p

refine : a -> (p : a -> Bool) -> Maybe (Refined a p)
refine x p = if p x then just (unsafeRefine x) else nothing

unrefine : {p : a -> Bool} -> Refined a p -> a
unrefine (unsafeRefine x) = x