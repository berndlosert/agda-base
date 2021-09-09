{-# OPTIONS --type-in-type #-}

module Data.Monoid.Endo where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import String.Show

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
  constructor toEndo
  field appEndo : a -> a

open Endo public

instance
  Semigroup-Endo : Semigroup (Endo a)
  Semigroup-Endo ._<>_ g f = toEndo (appEndo g <<< appEndo f)

  Monoid-Endo : Monoid (Endo a)
  Monoid-Endo .neutral = toEndo id
