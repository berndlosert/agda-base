{-# OPTIONS --type-in-type #-}

module Data.Decimal where

-- The natural numbers represented as a list of digits with the least
-- significant digit first.

open import Data.Digit public
open import Data.List public

Decimal : Set
Decimal = List Digit

-- This allows us to use _+_ for adding decimals.

open import Notation.Add public

instance
  Add:Decimal : Add Decimal
  Add:Decimal ._+_ m n = add m n 0d
    where

      -- Add two decimal numbers and a carry digit following the school-taught
      -- algorithm.

      add : Decimal -> Decimal -> Digit -> Decimal
      add [] [] 0d = [] -- prevents adding leading zeros
      add [] [] carry = [ carry ]
      add [] (n :: ns) carry =
        let (sum , carry') = Digit.halfAdd n carry
        in sum :: add [] ns carry'
      add (m :: ms) [] carry =
        let (sum , carry') = Digit.halfAdd m carry
        in sum :: add ms [] carry'
      add (m :: ms) (n :: ns) carry =
        let (sum , carry') = Digit.fullAdd m n carry
        in sum :: add ms ns carry'

module Decimal where

  open import Data.Nat

  fromNat : Nat -> Decimal
  fromNat zero = [ 0d ]
  fromNat (suc n) = fromNat n + [ 1d ]

  toNat : Decimal -> Nat
  toNat [] = 0
  toNat (d :: ds) = Digit.toNat d + 10 * toNat ds
