{-# OPTIONS --type-in-type #-}

module Data.Range where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

-------------------------------------------------------------------------------
-- Range
-------------------------------------------------------------------------------

record Range (a : Set) : Set where
  field
    rangeSize : a * a -> Nat
    range : a * a -> List a
    inRange : a * a -> a -> Bool

open Range {{...}} public

instance
  Range-Nat : Range Nat
  Range-Nat .rangeSize (m , n) = max (m - n) (n - m) + 1
  Range-Nat .range (m , n) =
      let k = rangeSize (m , n) - 1
      in go k m n
    where
      go : Nat -> Nat -> Nat -> List Nat
      go 0 m _ = [ m ]
      go (Suc k) m n =
        let m' = if m < n then m + 1 else (m - 1)
        in m :: go k m' n
  Range-Nat .inRange (m , n) k = m <= k && k <= n

  Range-Int : Range Int
  Range-Int .rangeSize (m , n) = toNat (abs (m - n)) {{believeMe}} + 1
  Range-Int .range (m , n) =
      let k = rangeSize (m , n) - 1
      in go k m n
    where
      go : Nat -> Int -> Int -> List Int
      go 0 m _ = [ m ]
      go (Suc k) m n =
        let m' = if m < n then m + 1 else (m - 1)
        in m :: go k m' n
  Range-Int .inRange (m , n) k = m <= k && k <= n

  Range-Char : Range Char
  Range-Char .rangeSize (c , d) = rangeSize (ord c , ord d)
  Range-Char .range (c , d) = chr <$> range (ord c , ord d)
  Range-Char .inRange (c , d) x = inRange (ord c , ord d) (ord x)
