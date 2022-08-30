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
    a : Set

-------------------------------------------------------------------------------
-- Endo
-------------------------------------------------------------------------------

record Endo (a : Set) : Set where
  constructor asEndo
  field appEndo : a -> a

open Endo public

instance
  Semigroup-Endo : Semigroup (Endo a)
  Semigroup-Endo ._<>_ g f = asEndo (appEndo g <<< appEndo f)

  Monoid-Endo : Monoid (Endo a)
  Monoid-Endo .mempty = asEndo id
