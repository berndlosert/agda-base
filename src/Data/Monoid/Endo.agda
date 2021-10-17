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
  constructor anEndo
  field appEndo : a -> a

open Endo public

instance
  Semigroup-Endo : Semigroup (Endo a)
  Semigroup-Endo ._<>_ g f = anEndo (appEndo g <<< appEndo f)

  Monoid-Endo : Monoid (Endo a)
  Monoid-Endo .mempty = anEndo id
