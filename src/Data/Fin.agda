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

module _ {n : Nat} where
  instance
    Eq-Fin : Eq (Fin n)
    Eq-Fin ._==_ (Fin: k) (Fin: m) = unsafePerform $
      rem k n == rem m n

    Ord-Fin : Ord (Fin n)
    Ord-Fin .compare (Fin: k) (Fin: m) = unsafePerform $
      compare (rem k n) (rem m n)

    FromNat-Fin : FromNat (Fin n)
    FromNat-Fin .FromNatConstraint _ = Unit
    FromNat-Fin .fromNat m = Fin: m

    ToNat-Fin : ToNat (Fin n)
    ToNat-Fin .ToNatConstraint _ = Unit
    ToNat-Fin .toNat (Fin: m) = unsafePerform $ rem m n

    Num-Fin : Num (Fin n)
    Num-Fin ._+_ (Fin: k) (Fin: m) = unsafePerform $
      Fin: $ rem (k + m) n
    Num-Fin ._-_ (Fin: k) (Fin: m) = unsafePerform $
      Fin: $ if k >= m then rem (monus k m) n else monus n (rem (monus m k) n)
    Num-Fin ._*_ (Fin: k) (Fin: m) = unsafePerform $
      Fin: $ rem (k * m) n

    Show-Fin : Show (Fin n)
    Show-Fin .showsPrec _ m = showString $ show $ toNat m
