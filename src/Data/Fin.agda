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

data Fin (n : Nat) : Type where
  Fin: : (m : Nat) -> Fin n

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

module _ {n : Nat} {{_ : Assert $ nonzero n}} where
  instance
    Eq-Fin : Eq (Fin n)
    Eq-Fin ._==_ (Fin: k) (Fin: m) = unsafePerform $ mod k n == mod m n

    Ord-Fin : Ord (Fin n)
    Ord-Fin .compare (Fin: k) (Fin: m) =
      unsafePerform $ compare (mod k n) (mod m n)

    FromNat-Fin : FromNat (Fin n)
    FromNat-Fin .FromNatConstraint _ = Unit
    FromNat-Fin .fromNat m = Fin: m

    ToNat-Fin : ToNat (Fin n)
    ToNat-Fin .ToNatConstraint _ = Unit
    ToNat-Fin .toNat (Fin: m) = unsafePerform $ mod m n

    Num-Fin : Num (Fin n)
    Num-Fin .nonzero (Fin: m) = nonzero m
    Num-Fin ._+_ (Fin: k) (Fin: m) = Fin: $ unsafePerform $ mod (k + m) n
    Num-Fin ._-_ (Fin: k) (Fin: m) = Fin: $ unsafePerform $
      if k >= m then mod (k - m) n else n - mod (m - k) n
    Num-Fin ._*_ (Fin: k) (Fin: m) = Fin: $ unsafePerform $ mod (k * m) n

    Show-Fin : Show (Fin n)
    Show-Fin .showsPrec _ m = showString $ show $ toNat m
