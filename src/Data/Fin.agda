module Data.Fin where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

-------------------------------------------------------------------------------
-- Fin
-------------------------------------------------------------------------------

data Fin (n : Nat) {{_ : Assert $ n > 0}} : Set where
  aFin : (m : Nat) -> Fin n

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

module _ {n : Nat} where
  instance
    Eq-Fin : Eq (Fin (suc n))
    Eq-Fin ._==_ (aFin k) (aFin m) = k % suc n == m % suc n

    Ord-Fin : Ord (Fin (suc n))
    Ord-Fin ._<_ (aFin k) (aFin m) = k % suc n < m % suc n

    FromNat-Fin : FromNat (Fin (suc n))
    FromNat-Fin .fromNat m = aFin m

    ToNat-Fin : ToNat (Fin (suc n))
    ToNat-Fin .toNat (aFin m) = m % suc n

    HasAdd-Fin : HasAdd (Fin (suc n))
    HasAdd-Fin ._+_ (aFin k) (aFin m) = aFin $ (k + m) % suc n

    HasSub-Fin : HasSub (Fin (suc n))
    HasSub-Fin .Diff = Fin (suc n)
    HasSub-Fin ._-_ (aFin k) (aFin m) =
      aFin $ if k >= m then (k - m) % suc n else n - ((m - k) % suc n)

    HasMul-Fin : HasMul (Fin (suc n))
    HasMul-Fin ._*_ (aFin k) (aFin m) = aFin $ (k * m) % suc n

    Show-Fin : Show (Fin (suc n))
    Show-Fin .showsPrec _ m = showString $ show $ toNat m
