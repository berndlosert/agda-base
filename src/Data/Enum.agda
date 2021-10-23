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
    prev : a -> a

  enumFromTo : a -> a -> List a
  enumFromTo = fix \ where
    go x y -> case compare x y of \ where
      EQ -> x :: []
      LT -> x :: go (next x) y
      GT -> x :: go (prev x) y

open Enum {{...}} public

instance
  Enum-Nat : Enum Nat
  Enum-Nat .next = suc
  Enum-Nat .prev 0 = 0
  Enum-Nat .prev (suc n) = n

  Enum-Int : Enum Int
  Enum-Int .next (pos n) = pos (suc n)
  Enum-Int .next (negsuc n) = neg n
  Enum-Int .prev (pos 0) = negsuc 0
  Enum-Int .prev (pos (suc n)) = pos n
  Enum-Int .prev (negsuc n) = negsuc (suc n)

  Enum-Char : Enum Char
  Enum-Char .next c = if c == maxChar then c else chr $ next (ord c)
  Enum-Char .prev c = if c == minChar then c else chr $ prev (ord c)
