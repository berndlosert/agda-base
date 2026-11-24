module Data.Nat.Positive where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

-------------------------------------------------------------------------------
-- Nat1
-------------------------------------------------------------------------------

data Nat1 : Type where
  suc : Nat -> Nat1

instance
  Eq-Nat1 : Eq Nat1
  Eq-Nat1 ._==_ (suc k) (suc m) = k == m

  Ord-Nat1 : Ord Nat1
  Ord-Nat1 ._<_ (suc k) (suc m) = k < m

  ToNat-Nat1 : ToNat Nat1
  ToNat-Nat1 .toNat (suc m) = suc m

  Addable-Nat1 : Addable Nat1
  Addable-Nat1 ._+_ (suc m) (suc n) = suc (suc (m + n))

  Multiplicative-Nat1 : Multiplicative Nat1
  Multiplicative-Nat1 ._*_ (suc m) (suc n) = suc (m * n + m + n)

  Subtractable-Nat1 : Subtractable Nat1
  Subtractable-Nat1 ._-_ (suc m) (suc n) with m - n
  ... | 0 = suc 0
  ... | suc k = suc k

FromNat-Nat1 : FromNat Nat1
FromNat-Nat1 .FromNat.Constraint 0 = Void
FromNat-Nat1 .FromNat.Constraint _ = Unit
FromNat-Nat1 .fromNat (suc n) = suc n
