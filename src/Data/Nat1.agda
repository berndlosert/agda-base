{-# OPTIONS --type-in-type #-}

module Data.Nat1 where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

-------------------------------------------------------------------------------
-- Nat1
-------------------------------------------------------------------------------

data Nat1 : Set where
  One : Nat1
  Suc : Nat1 -> Nat1

instance
  FromNat-Nat1 : FromNat Nat1
  FromNat-Nat1 .FromNatConstraint 0 = Void
  FromNat-Nat1 .FromNatConstraint _ = Unit
  FromNat-Nat1 .fromNat (Suc 0) = One
  FromNat-Nat1 .fromNat (Suc n@(Suc _)) = Suc (fromNat n)

  ToNat-Nat1 : ToNat Nat1
  ToNat-Nat1 .ToNatConstraint _ = Unit
  ToNat-Nat1 .toNat One = 1
  ToNat-Nat1 .toNat (Suc n) = Suc (toNat n)

  Eq-Nat1 : Eq Nat1
  Eq-Nat1 ._==_ m n = toNat m == toNat n

  Ord-Nat1 : Ord Nat1
  Ord-Nat1 .compare m n = compare (toNat m) (toNat n)

  Show-Nat1 : Show Nat1
  Show-Nat1 .showsPrec _ n = showString $ show $ toNat n
