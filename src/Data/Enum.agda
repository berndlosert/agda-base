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
    next : a -> Maybe a
    prev : a -> Maybe a

  enumFromTo : a -> a -> List a
  enumFromTo x y =
    case compare x y of \ where
      EQ -> x :: []
      LT -> case next x of \ where
        (just x') -> x :: enumFromTo x' y
        nothing -> x :: []
      GT -> case prev x of \ where
        (just x') -> x :: enumFromTo x' y
        nothing -> x :: []

open Enum {{...}} public

instance
  Enum-Nat : Enum Nat
  Enum-Nat .next = just <<< suc
  Enum-Nat .prev 0 = nothing
  Enum-Nat .prev (suc n) = just n

  Enum-Int : Enum Int
  Enum-Int .next (pos n) = just (pos (suc n))
  Enum-Int .next (negsuc n) = just (neg n)
  Enum-Int .prev (pos 0) = just (negsuc 0)
  Enum-Int .prev (pos (suc n)) = just (pos n)
  Enum-Int .prev (negsuc n) = just (negsuc (suc n))

  Enum-Char : Enum Char
  Enum-Char .next maxChar = nothing
  Enum-Char .next c = next (ord c) >>= chr
  Enum-Char .prev minChar = nothing
  Enum-Char .prev c = prev (ord c) >>= chr
