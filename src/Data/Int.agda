{-# OPTIONS --type-in-type #-}

module Data.Int where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

-------------------------------------------------------------------------------
-- Functions
-------------------------------------------------------------------------------

neg : Nat -> Int
neg 0 = Pos 0
neg (Suc n) = NegSuc n

diff : Nat -> Nat -> Int
diff m Zero = Pos m
diff Zero (Suc n) = NegSuc n
diff (Suc m) (Suc n) = diff m n

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

instance
  Eq-Int : Eq Int
  Eq-Int ._==_ = \ where
    (Pos m) (Pos n) -> m == n
    (NegSuc m) (NegSuc n) -> m == n
    _ _ -> False

  Ord-Int : Ord Int
  Ord-Int .compare = \ where
    (Pos m) (Pos n) -> compare m n
    (NegSuc m) (NegSuc n) -> compare n m
    (Pos _) (NegSuc _) -> GT
    (NegSuc _) (Pos _) -> LT

  FromNat-Int : FromNat Int
  FromNat-Int .FromNatConstraint _ = Unit
  FromNat-Int .fromNat n = Pos n

  ToNat-Int : ToNat Int
  ToNat-Int .ToNatConstraint _ = Unit
  ToNat-Int .toNat (Pos n) = n
  ToNat-Int .toNat (NegSuc n) = 0

  FromNeg-Int : FromNeg Int
  FromNeg-Int .FromNegConstraint _ = Unit
  FromNeg-Int .fromNeg n = neg n

  Validation-Positive-Int : Validation Positive Int
  Validation-Positive-Int .validate _ = \ where
    (Pos 0) -> False
    (NegSuc _) -> False
    _ -> True

  Validation-Nonzero-Int : Validation Nonzero Int
  Validation-Nonzero-Int .validate _ = \ where
    (Pos 0) -> False
    _ -> True

  Num-Int : Num Int
  Num-Int ._+_ = \ where
    (NegSuc m) (NegSuc n) -> NegSuc (Suc (m + n))
    (NegSuc m) (Pos n) -> diff n (Suc m)
    (Pos m) (NegSuc n) -> diff m (Suc n)
    (Pos m) (Pos n) -> Pos (m + n)
  Num-Int ._-_ = \ where
    m (Pos n) -> m + neg n
    m (NegSuc n) -> m + Pos (Suc n)
  Num-Int ._*_ = \ where
    (Pos n) (Pos m) -> Pos (n * m)
    (NegSuc n) (NegSuc m) -> Pos (Suc n * Suc m)
    (Pos n) (NegSuc m) -> neg (n * Suc m)
    (NegSuc n) (Pos m) -> neg (Suc n * m)

  Signed-Int : Signed Int
  Signed-Int .-_ = \ where
    (Pos 0) -> Pos 0
    (Pos (Suc n)) -> NegSuc n
    (NegSuc n) -> Pos (Suc n)
  Signed-Int .abs n@(Pos _) = n
  Signed-Int .abs (NegSuc n) = Pos (Suc n)
  Signed-Int .signum n@(Pos 0) = n
  Signed-Int .signum (Pos _) = Pos 1
  Signed-Int .signum (NegSuc _) = NegSuc 0

  Integral-Int : Integral Int
  Integral-Int .div = \ where
    (Pos m) (Pos n@(Suc _)) -> Pos (div m n)
    (Pos m) (NegSuc n) -> neg (div m (Suc n))
    (NegSuc m) (Pos n@(Suc _)) -> neg (div (Suc m) n)
    (NegSuc m) (NegSuc n) -> Pos (div (Suc m) (Suc n))
    _ _ -> undefined
  Integral-Int .mod = \ where
    (Pos m) (Pos n@(Suc _)) -> Pos (mod m n)
    (Pos m) (NegSuc n) -> Pos (mod m (Suc n))
    (NegSuc m) (Pos n@(Suc _)) -> neg (mod (Suc m) n)
    (NegSuc m) (NegSuc n) -> neg (mod (Suc m) (Suc n))
    _ _ -> undefined
