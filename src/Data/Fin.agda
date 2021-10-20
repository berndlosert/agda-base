module Data.Fin where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

-------------------------------------------------------------------------------
-- Fin
-------------------------------------------------------------------------------

data Fin (n : Nat) {{_ : Assert $ divisor n}} : Set where
  toFin : (m : Nat) -> Fin n

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

module _ {n : Nat} {{_ : Assert $ divisor n}} where
  instance
    Eq-Fin : Eq (Fin n)
    Eq-Fin ._==_ (toFin k) (toFin m) = k % n == m % n

    Ord-Fin : Ord (Fin n)
    Ord-Fin ._<_ (toFin k) (toFin m) = k % n < m % n

    FromNat-Fin : FromNat (Fin n)
    FromNat-Fin .FromNatConstraint _ = Unit
    FromNat-Fin .fromNat m = toFin m

    ToNat-Fin : ToNat (Fin n)
    ToNat-Fin .ToNatConstraint _ = Unit
    ToNat-Fin .toNat (toFin m) = m % n

    HasAdd-Fin : HasAdd (Fin n)
    HasAdd-Fin ._+_ (toFin k) (toFin m) = toFin $ (k + m) % n

    HasSub-Fin : HasSub (Fin n)
    HasSub-Fin .Diff = Fin n
    HasSub-Fin ._-_ (toFin k) (toFin m) =
      toFin $ if k >= m then (k - m) % n else n - ((m - k) % n)

    HasMul-Fin : HasMul (Fin n)
    HasMul-Fin ._*_ (toFin k) (toFin m) = toFin $ (k * m) % n

    Show-Fin : Show (Fin n)
    Show-Fin .showsPrec _ m = showString $ show $ toNat m
