{-# OPTIONS --type-in-type #-}

module Data.Fin where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Data.Nat as Nat using ()
open import String.Show

-------------------------------------------------------------------------------
-- Fin
-------------------------------------------------------------------------------

data Fin (n : Nat) {{_ : Nonzero n}} : Type where
  Fin: : (m : Nat) -> Fin n

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

instance
  Eq-Fin : {n : Nat} {{_ : Nonzero n}} -> Eq (Fin n)
  Eq-Fin {n} ._==_ (Fin: k) (Fin: m) = mod k n == mod m n

  Ord-Fin : {n : Nat} {{_ : Nonzero n}} -> Ord (Fin n)
  Ord-Fin {n} .compare (Fin: k) (Fin: m) = compare (mod k n) (mod m n)

  FromNat-Fin : {n : Nat} {{_ : Nonzero n}} -> FromNat (Fin n)
  FromNat-Fin .FromNatConstraint _ = Unit
  FromNat-Fin .fromNat m = Fin: m

  ToNat-Fin : {n : Nat} {{_ : Nonzero n}} -> ToNat (Fin n)
  ToNat-Fin .ToNatConstraint _ = Unit
  ToNat-Fin {n} .toNat (Fin: m) = mod m n

  Num-Fin : {n : Nat} {{_ : Nonzero n}} -> Num (Fin n)
  Num-Fin .nonzero (Fin: m) = nonzero m
  Num-Fin {n} ._+_ (Fin: k) (Fin: m) = Fin: (mod (k + m) n)
  Num-Fin {n} ._-_ (Fin: k) (Fin: m) =
    if k >= m
      then Fin: $ mod (k - m) n
      else Fin: $ n - mod (m - k) n
  Num-Fin {n} ._*_ (Fin: k) (Fin: m) = Fin: (mod (k * m) n)

  Show-Fin : {n : Nat} {{_ : Nonzero n}} -> Show (Fin n)
  Show-Fin {n} .showsPrec _ m = showString $ show $ toNat m
