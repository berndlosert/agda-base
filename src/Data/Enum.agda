{-# OPTIONS --type-in-type #-}

module Data.Enum where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Data.Bounds
open import Data.Char

-------------------------------------------------------------------------------
-- Enum
-------------------------------------------------------------------------------

record Enum (a : Set) : Set where
  field
    overlap {{Bounds-super}} : Bounds a
    next : a -> a
    previous : a -> a

  enumFromTo : a -> a -> List a
  enumFromTo = fix \ where
    enumFromTo x y -> case compare x y of \ where
      EQ -> x :: []
      LT -> x :: enumFromTo (next x) y
      GT -> x :: enumFromTo (previous x) y

open Enum {{...}} public

instance
  Enum-Nat : Enum Nat
  Enum-Nat .next = suc
  Enum-Nat .previous = pred

  Enum-Int : Enum Int
  Enum-Int .next (pos n) = pos (suc n)
  Enum-Int .next (negsuc n) = neg n
  Enum-Int .previous (pos 0) = negsuc 0
  Enum-Int .previous (pos (suc n)) = pos n
  Enum-Int .previous (negsuc n) = negsuc (suc n)

  Enum-Char : Enum Char
  Enum-Char .next c = if c == maxChar then c else chr $ next (ord c)
  Enum-Char .previous c = if c == minChar then c else chr $ previous (ord c)
