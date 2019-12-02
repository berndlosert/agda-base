{-# OPTIONS --type-in-type #-}

module Data.Decimal where

-- The natural numbers represented as a list of digits with the least
-- significant digit first.

open import Data.Digit
open import Data.List.Base

Decimal : Set
Decimal = List Digit

-- Add two decimal numbers and a carry digit following the school-taught
-- algorithm.

open import Data.Product

private
  add : Decimal -> Decimal -> Digit -> Decimal
  add [] [] 0d = [] -- prevents adding leading zeros
  add [] [] carry = [ carry ]
  add [] (n :: ns) carry =
    let (sum , carry') = halfAdd n carry
    in sum :: add [] ns carry'
  add (m :: ms) [] carry =
    let (sum , carry') = halfAdd m carry
    in sum :: add ms [] carry'
  add (m :: ms) (n :: ns) carry =
    let (sum , carry') = fullAdd m n carry
    in sum :: add ms ns carry'

-- This allows us to use _+_ for adding decimals.

open import Notation.Add

instance
  Add:Decimal : Add Decimal
  Add:Decimal = Add: (\ m n -> add m n 0d)

-- This converts a unary natural number to a decimal number.

open import Data.Cast
open import Data.Nat.Base

instance
  NatToDecimal : Cast Nat Decimal
  NatToDecimal .cast zero = [ 0d ]
  NatToDecimal .cast (suc n) = cast n + [ 1d ]

-- Cast Decimal to Nat.

instance
  DecimalToNat : Cast Decimal Nat
  DecimalToNat .cast [] = 0
  DecimalToNat .cast (d :: ds) = cast d + 10 * cast ds

-- This allows us to use natural number literals to write decimals.

open import Data.Unit public
open import Notation.Number public

Number:Decimal : Number Decimal
Number:Decimal = record {
    Constraint = \ _ -> Unit;
    fromNat = \ n -> cast n
  }

-- Convert a list of digit characters to a decimal number.

open import Data.Char
open import Data.Maybe
open import Data.List
open import Data.Traversable

instance
  CharsToDecimal : Cast (List Char) (Maybe Decimal)
  CharsToDecimal .cast ds = traverse cast (reverse ds)
