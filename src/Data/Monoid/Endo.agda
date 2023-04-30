module Data.Monoid.Endo where

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
-- Endo
-------------------------------------------------------------------------------

record Endo (a : Type) : Type where
  constructor asEndo
  field appEndo : a -> a

open Endo public

diff : {{Semigroup a}} -> a -> Endo a
diff x = asEndo (x <>_)

instance
  Semigroup-Endo : Semigroup (Endo a)
  Semigroup-Endo ._<>_ g f = asEndo (appEndo g <<< appEndo f)

  Monoid-Endo : Monoid (Endo a)
  Monoid-Endo .mempty = asEndo id
