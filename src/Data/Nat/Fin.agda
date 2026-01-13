module Data.Nat.Fin where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Data.String.Show

-------------------------------------------------------------------------------
-- Fin
-------------------------------------------------------------------------------

abstract
  Fin : Nat -> Type
  Fin _ = Nat

  fromFin : {n : Nat} -> Fin n -> Nat
  fromFin m = m

  private
    unsafeFin : (n m : Nat) -> Fin n
    unsafeFin _ m = m

fin : (n m : Nat) -> {{Assert (n > 0)}} -> Fin n
fin n m = unsafeFin n (mod m n)

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

module _ {n : Nat} {{_ : Assert (n > 0)}} where
  instance
    ToNat-Fin : ToNat (Fin n)
    ToNat-Fin .toNat = fromFin

    FromNat-Fin : FromNat (Fin n)
    FromNat-Fin .FromNat.Constraint _ = Unit
    FromNat-Fin .fromNat m = fin n m

    Eq-Fin : Eq (Fin n)
    Eq-Fin ._==_ k m = toNat k == toNat m

    Ord-Fin : Ord (Fin n)
    Ord-Fin ._<_ k m = toNat k < toNat m

    Addable-Fin : Addable (Fin n)
    Addable-Fin ._+_ k m = fin n (toNat k + toNat m)

    Multiplicable-Fin : Multiplicable (Fin n)
    Multiplicable-Fin ._*_ k m = fin n (toNat k * toNat m)

    Subtractable-Fin : Subtractable (Fin n)
    Subtractable-Fin ._-_ k m = fin n $
      if k >= m
        then toNat k - toNat m
        else n - toNat m - toNat k

    Negatable-Fin : Negatable (Fin n)
    Negatable-Fin .-_ k = 0 - k

    Exponentiable-Fin : Exponentiable (Fin n)
    Exponentiable-Fin .Power = Nat
    Exponentiable-Fin ._^_ k m = fin n ((toNat k) ^ m)

    Show-Fin : Show (Fin n)
    Show-Fin .show m = show (toNat m)
    Show-Fin .showsPrec = showsPrecDefault
