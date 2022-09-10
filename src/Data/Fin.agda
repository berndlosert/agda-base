module Data.Fin where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

-------------------------------------------------------------------------------
-- Fin
-------------------------------------------------------------------------------

data Fin (n : Nat) : Set where
  -- m is assumed to be < n.
  unsafeFin : (m : Nat) -> Fin n

asFin : (n m : Nat) -> Fin n
asFin n m = unsafeFin (m % n)

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

    HasAdd-Fin : HasAdd (Fin n)
    HasAdd-Fin ._+_ k m = asFin n (toNat k + toNat m)

    HasSub-Fin : HasSub (Fin n)
    HasSub-Fin ._-_ k m = asFin n $
      if k >= m then (toNat k - toNat m) else n - ((toNat m - toNat k))

    HasMul-Fin : HasMul (Fin n)
    HasMul-Fin ._*_ k m = asFin n $ (toNat k * toNat m)

    Show-Fin : Show (Fin n)
    Show-Fin .showsPrec _ m = showString $ show $ toNat m
