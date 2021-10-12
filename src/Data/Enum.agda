{-# OPTIONS --type-in-type #-}

module Data.Enum where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Data.Char

-------------------------------------------------------------------------------
-- Enum
-------------------------------------------------------------------------------

record Enum (a : Set) : Set where
  field
    {{Ord-super}} : Ord a
    next : a -> Maybe a
    previous : a -> Maybe a
    enumFromTo : a -> a -> List a

open Enum {{...}} public

instance
  Enum-Nat : Enum Nat
  Enum-Nat .next x = just (suc x)
  Enum-Nat .previous 0 = nothing
  Enum-Nat .previous (suc n) = just n
  Enum-Nat .enumFromTo = fix \ where
    go m n -> case compare m n of \ where
      EQ -> m :: []
      LT -> m :: go (suc m) n
      GT -> m :: go (pred m) n

  Enum-Int : Enum Int
  Enum-Int .next (pos n) = just $ pos (suc n)
  Enum-Int .next (negsuc n) = just $ neg n
  Enum-Int .previous (pos 0) = just $ negsuc 0
  Enum-Int .previous (pos (suc n)) = just $ pos n
  Enum-Int .previous (negsuc n) = just $ negsuc (suc n)
  Enum-Int .enumFromTo m n =
    case m - n of \ where
      (pos k) -> (\ i -> pos i + n) <$> enumFromTo k 0
      (negsuc k) -> (\ i -> pos i + m) <$> enumFromTo 0 (suc k)

  Enum-Char : Enum Char
  Enum-Char .next c =
    if c == maxChar
      then nothing
      else chr <$> next (ord c)
  Enum-Char .previous c =
    if c == minChar
      then nothing
      else chr <$> previous (ord c)
  Enum-Char .enumFromTo c d = chr <$> enumFromTo (ord c) (ord d)
