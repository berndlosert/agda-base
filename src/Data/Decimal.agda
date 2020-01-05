{-# OPTIONS --type-in-type #-}

module Data.Decimal where

-- The natural numbers represented as a list of digits with the least
-- significant digit first.

open import Data.Digit
open import Data.List

Decimal : Set
Decimal = List Digit

module Decimal where

  -- Add two decimal numbers and a carry digit following the school-taught
  -- algorithm.
  
  open import Data.Digit
  open import Data.List
  open import Data.Product
  
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
  
  -- This allows us to use _+_ for adding decimals.
  
  open import Notation.Add
  
  instance
    Add:Decimal : Add Decimal
    Add:Decimal = Add: (\ m n -> add m n 0d)
  
  -- Convert a unary natural number to a decimal number.
  
  open import Data.Nat
  
  fromNat : Nat -> Decimal
  fromNat zero = [ 0d ]
  fromNat (suc n) = fromNat n + [ 1d ]
  
  -- Convert a decimal number to a unary natural number.
  
  open import Notation.Mul

  instance _ = Number:Nat

  toNat : Decimal -> Nat
  toNat [] = 0
  toNat (d :: ds) = Digit.toNat d + 10 * toNat ds

open Decimal public
  using (Add:Decimal)
