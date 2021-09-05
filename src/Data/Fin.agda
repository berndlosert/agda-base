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

data Fin (n : Nat) {{_ : Assert $ divisor n}} : Set where
  Fin: : (m : Nat) -> Fin n

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

module _ {n : Nat} {{_ : Assert $ divisor n}} where
  instance
    Eq-Fin : Eq (Fin n)
    Eq-Fin ._==_ (Fin: k) (Fin: m) = k % n == m % n

    Ord-Fin : Ord (Fin n)
    Ord-Fin .compare (Fin: k) (Fin: m) = compare (k % n) (m % n)

    FromNat-Fin : FromNat (Fin n)
    FromNat-Fin .FromNatConstraint _ = Unit
    FromNat-Fin .fromNat m = Fin: m

    ToNat-Fin : ToNat (Fin n)
    ToNat-Fin .ToNatConstraint _ = Unit
    ToNat-Fin .toNat (Fin: m) = m % n

    Add-Fin : Add (Fin n)
    Add-Fin ._+_ (Fin: k) (Fin: m) = Fin: $ (k + m) % n

    Sub-Fin : Sub (Fin n)
    Sub-Fin .Diff = Fin n
    Sub-Fin ._-_ (Fin: k) (Fin: m) =
      Fin: $ if k >= m then (k - m) % n else n - ((m - k) % n)

    Mul-Fin : Mul (Fin n)
    Mul-Fin ._*_ (Fin: k) (Fin: m) = Fin: $ (k * m) % n

    Show-Fin : Show (Fin n)
    Show-Fin .showsPrec _ m = showString $ show $ toNat m
