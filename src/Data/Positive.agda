{-# OPTIONS --type-in-type #-}

module Data.Positive where

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
-- Positiveness
-------------------------------------------------------------------------------

record Positiveness (a : Set) : Set where
  field positive : a -> Bool

open Positiveness {{...}} public

instance
  Positiveness-Nat : Positiveness Nat
  Positiveness-Nat .positive 0 = false
  Positiveness-Nat .positive _ = true

  Positiveness-Int : Positiveness Int
  Positiveness-Int .positive (pos 0) = false
  Positiveness-Int .positive (negsuc _) = false
  Positiveness-Int .positive _ = true

  Positiveness-Float : Positiveness Float
  Positiveness-Float .positive = _> 0

-------------------------------------------------------------------------------
-- Positive
-------------------------------------------------------------------------------

record Positive (a : Set) {{_ : Positiveness a}} : Set where
  constructor aPositive
  field
    fromPositive : a
    {{Assert-positive}} : Assert (positive fromPositive)

open Positive
