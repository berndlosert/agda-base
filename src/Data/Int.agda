{-# OPTIONS --type-in-type #-}

module Data.Int where

import Data.Nat as Nat
import Prelude

open Prelude

toNat : Int -> Nat
toNat (pos n) = n
toNat (negsuc n) = suc n

-- The absolute value of an Int.
abs : Int -> Int
abs n = pos (toNat n)

-- Determine if a integer is even or odd.
even : Int -> Bool
even (pos n) = Nat.even n
even (negsuc n) = Nat.odd n

odd : Int -> Bool
odd n = not (even n)
