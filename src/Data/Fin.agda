module Data.Fin where

open import Prelude

private variable n : Nat

data Fin : Nat -> Set where
  Zero : Fin (Suc n)
  Suc : Fin n -> Fin (Suc n)

-- Convert a Fin n into a Nat.
toNat : Fin n -> Nat
toNat Zero = 0
toNat (Suc n) = Suc (toNat n)

instance
  FromNat-Fin : forall {n} -> FromNat (Fin (Suc n))
  FromNat-Fin {n} .FromNatConstraint m = Assert (m <= n)
  FromNat-Fin {n} .fromNat m {{p}} = go m n {p}
    where
      go : (m n : Nat) {_ : Assert (m <= n)} -> Fin (Suc n)
      go Zero _ = Zero
      go (Suc m) (Suc n) {p} = Suc (go m n {p})
