{-# OPTIONS --type-in-type #-}

module Data.Fin where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import String.Show

-------------------------------------------------------------------------------
-- Fin
-------------------------------------------------------------------------------

data Fin (n : Nat) : Set where
  Fin: : (m : Nat) -> Fin n

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

module _ {n : Nat} {{_ : Validate NonZero n}} where
  instance
    Eq-Fin : Eq (Fin n)
    Eq-Fin ._==_ (Fin: k) (Fin: m) = mod k n == mod m n

    Ord-Fin : Ord (Fin n)
    Ord-Fin .compare (Fin: k) (Fin: m) = compare (mod k n) (mod m n)

    FromNat-Fin : FromNat (Fin n)
    FromNat-Fin .FromNatConstraint _ = Unit
    FromNat-Fin .fromNat m = Fin: m

    ToNat-Fin : ToNat (Fin n)
    ToNat-Fin .ToNatConstraint _ = Unit
    ToNat-Fin .toNat (Fin: m) = mod m n

    Num-Fin : Num (Fin n)
    Num-Fin ._+_ (Fin: k) (Fin: m) = Fin: $ mod (k + m) n
    Num-Fin ._-_ (Fin: k) (Fin: m) =
      Fin: $ if k >= m then mod (k - m) n else n - mod (m - k) n
    Num-Fin ._*_ (Fin: k) (Fin: m) = Fin: $ mod (k * m) n

    Show-Fin : Show (Fin n)
    Show-Fin .showsPrec _ m = showString $ show $ toNat m
