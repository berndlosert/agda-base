{-# OPTIONS --type-in-type #-}

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
  constructor Endo:
  field appEndo : a -> a

open Endo public

instance
  Semigroup-Endo : Semigroup (Endo a)
  Semigroup-Endo ._<>_ g f = Endo: \ x -> appEndo g (appEndo f x)

  Monoid-Endo : Monoid (Endo a)
  Monoid-Endo .mempty = Endo: \ x -> x
