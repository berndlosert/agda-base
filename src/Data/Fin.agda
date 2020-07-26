module Data.Fin where

open import Prelude
  hiding (Zero)

private variable n : Nat

data Fin : Nat -> Set where
  Zero : Fin (Suc n)
  Suc : Fin n -> Fin (Suc n)

-- Convert a Fin n into a Nat.
toNat : Fin n -> Nat
toNat Zero = 0
toNat (Suc n) = Suc (toNat n)

-- The Number:Fin instance allows us to write Fin n values using natural
-- number literals.
--instance
--  Number:Fin : forall {n} -> Number (Fin (Suc n))
--  Number:Fin {n} = record {
--      Constraint = λ m -> Assert (m <= n);
--      fromNat = λ m {{p}} -> go m n {p}
--    }
--    where
--      go : forall m n -> {_ : Assert (m <= n)} -> Fin (Suc n)
--      go Zero _ = Zero
--      go (Suc m) (Suc n) {p} = Suc (go m n {p})
