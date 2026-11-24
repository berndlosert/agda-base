module Data.Functor.Identity where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b : Type

-------------------------------------------------------------------------------
-- Identity
-------------------------------------------------------------------------------

record Identity (a : Type) : Type where
  constructor asIdentity
  field runIdentity : a

open Identity public

instance
  Eq-Identity : {{Eq a}} -> Eq (Identity a)
  Eq-Identity {a} ._==_ x y = runIdentity x == runIdentity y

  Ord-Identity : {{Ord a}} -> Ord (Identity a)
  Ord-Identity {a} ._<_ x y = runIdentity x < runIdentity y
