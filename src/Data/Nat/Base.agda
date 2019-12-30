{-# OPTIONS --type-in-type #-}

module Data.Nat.Base where

-- The type Nat of unary natural numbers has two constructors: zero
-- (for 0) and suc (for successor).

open import Agda.Builtin.Nat public
  using (Nat; zero; suc)
