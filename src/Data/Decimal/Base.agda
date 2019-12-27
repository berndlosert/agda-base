{-# OPTIONS --type-in-type #-}

module Data.Decimal.Base where

-- The natural numbers represented as a list of digits with the least
-- significant digit first.

open import Data.Digit
open import Data.List

Decimal : Set
Decimal = List Digit
