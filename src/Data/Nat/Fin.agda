module Data.Nat.Fin where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Data.String.Show

-------------------------------------------------------------------------------
-- Fin
-------------------------------------------------------------------------------

data Fin (n : Nat) : Set where
  -- m is assumed to be < n.
  unsafeFin : (m : Nat) -> Fin n

asFin : (n m : Nat) -> Fin n
asFin n m = unsafeFin (mod m n)

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

module _ {n : Nat} where
  instance
    ToNat-Fin : ToNat (Fin n)
    ToNat-Fin .toNat (unsafeFin m) = m

    FromNat-Fin : FromNat (Fin n)
    FromNat-Fin .fromNat m = asFin n m

    Eq-Fin : Eq (Fin n)
    Eq-Fin ._==_ k m = toNat k == toNat m

    Ord-Fin : Ord (Fin n)
    Ord-Fin ._<_ k m = toNat k < toNat m

    Num-Fin : Num (Fin n)
    Num-Fin ._+_ k m = asFin n (toNat k + toNat m)
    Num-Fin ._-_ k m = asFin n $
      if k >= m then (toNat k - toNat m) else n - ((toNat m - toNat k))
    Num-Fin .-_ k = 0 - k
    Num-Fin ._*_ k m = asFin n $ (toNat k * toNat m)
    Num-Fin ._^_ k m = asFin n $ (toNat k) ^ m

    Show-Fin : Show (Fin n)
    Show-Fin .show m = show (toNat m)
    Show-Fin .showsPrec = showsPrecDefault
