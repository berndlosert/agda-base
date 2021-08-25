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
    a : Type

-------------------------------------------------------------------------------
-- Endo
-------------------------------------------------------------------------------

record Endo (a : Type) : Type where
  constructor Endo:
  field appEndo : a -> a

open Endo public

instance
  Semigroup-Endo : Semigroup (Endo a)
  Semigroup-Endo ._<>_ g f = Endo: \ x -> appEndo g (appEndo f x)

  Monoid-Endo : Monoid (Endo a)
  Monoid-Endo .neutral = Endo: \ x -> x
