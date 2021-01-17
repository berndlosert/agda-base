{-# OPTIONS --type-in-type #-}

module Data.Fin where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    n : Nat

-------------------------------------------------------------------------------
-- Fin
-------------------------------------------------------------------------------

data Fin : Nat -> Set where
  Zero : Fin (Suc n)
  Suc : Fin n -> Fin (Suc n)

instance
  ToNat-Fin : ToNat (Fin n)
  ToNat-Fin .ToNatConstraint _ = Unit
  ToNat-Fin .toNat Zero = 0
  ToNat-Fin .toNat (Suc n) = Suc (toNat n)

  FromNat-Fin : FromNat (Fin (Suc n))
  FromNat-Fin {n} .FromNatConstraint m = Assert (m <= n)
  FromNat-Fin {n} .fromNat m {{p}} = go m n {p}
    where
      go : (m n : Nat) {_ : Assert (m <= n)} -> Fin (Suc n)
      go Zero _ = Zero
      go (Suc m) (Suc n) {p} = Suc (go m n {p})
