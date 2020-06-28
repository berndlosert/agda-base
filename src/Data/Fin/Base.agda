{-# OPTIONS --type-in-type #-}

module Data.Fin.Base where

open import Data.Nat public

-- The type Fin (Suc n) has n + 1 inhabitants, namely 0, 1, ..., n. Note that
-- Fin 0 is effectively the same as Void.

data Fin : Nat -> Set where
  Zero : {n : Nat} -> Fin (Suc n)
  Suc : {n : Nat} -> Fin n -> Fin (Suc n)
