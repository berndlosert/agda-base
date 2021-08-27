{-# OPTIONS --type-in-type #-}

module Data.Int where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Data.Nat as Nat using ()

-------------------------------------------------------------------------------
-- Int primitives
-------------------------------------------------------------------------------

neg : Nat -> Int
neg 0 = Pos 0
neg (Suc n) = NegSuc n

private
  intLessThan : Int -> Int -> Bool
  intLessThan (Pos m) (Pos n) = m < n
  intLessThan (NegSuc m) (NegSuc n) = n < m
  intLessThan (NegSuc _) (Pos _) = True
  intLessThan (Pos _) (NegSuc _) = False

  intNegate : Int -> Int
  intNegate = \ where
    (Pos Zero) -> Pos Zero
    (Pos (Suc n)) -> NegSuc n
    (NegSuc n) -> Pos (Suc n)

  intMinus : Nat -> Nat -> Int
  intMinus m Zero = Pos m
  intMinus Zero (Suc n) = NegSuc n
  intMinus (Suc m) (Suc n) = intMinus m n

  intPlus : Int -> Int -> Int
  intPlus (NegSuc m) (NegSuc n) = NegSuc (Suc (m + n))
  intPlus (NegSuc m) (Pos n) = intMinus n (Suc m)
  intPlus (Pos m) (NegSuc n) = intMinus m (Suc n)
  intPlus (Pos m) (Pos n) = Pos (m + n)

  intTimes : Int -> Int -> Int
  intTimes = \ where
    (Pos n) (Pos m) -> Pos (n * m)
    (NegSuc n) (NegSuc m) -> Pos (Suc n * Suc m)
    (Pos n) (NegSuc m) -> neg (n * Suc m)
    (NegSuc n) (Pos m) -> neg (Suc n * m)

  intDiv : {{Unsafe}} -> Int -> Int -> Int
  intDiv = \ where
    (Pos m) (Pos n@(Suc _)) -> Pos (div m n)
    (Pos m) (NegSuc n) -> neg (div m (Suc n))
    (NegSuc m) (Pos n@(Suc _)) -> neg (div (Suc m) n)
    (NegSuc m) (NegSuc n) -> Pos (div (Suc m) (Suc n))

  intMod : {{Unsafe}} -> Int -> Int -> Int
  intMod = \ where
    (Pos m) (Pos n@(Suc _)) -> Pos (mod m n)
    (Pos m) (NegSuc n) -> Pos (mod m (Suc n))
    (NegSuc m) (Pos n@(Suc _)) -> neg (mod (Suc m) n)
    (NegSuc m) (NegSuc n) -> neg (mod (Suc m) (Suc n))

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
  Ord-Int .compare i j =
    if i == j then EQ
    else if intLessThan i j then LT
    else GT

  FromNat-Int : FromNat Int
  FromNat-Int .FromNatConstraint _ = Unit
  FromNat-Int .fromNat n = Pos n

  ToNat-Int : ToNat Int
  ToNat-Int .ToNatConstraint n = Assert (n >= 0)
  ToNat-Int .toNat (Pos n) = n

  FromNeg-Int : FromNeg Int
  FromNeg-Int .FromNegConstraint _ = Unit
  FromNeg-Int .fromNeg n = neg n

  Num-Int : Num Int
  Num-Int .nonzero (Pos 0) = False
  Num-Int .nonzero _ = True
  Num-Int ._+_ = intPlus
  Num-Int ._-_ m n = m + intNegate n
  Num-Int ._*_ = intTimes

  Signed-Int : Signed Int
  Signed-Int .-_ = intNegate
  Signed-Int .abs n@(Pos _) = n
  Signed-Int .abs (NegSuc n) = Pos (Suc n)
  Signed-Int .signum n@(Pos 0) = n
  Signed-Int .signum (Pos _) = Pos 1
  Signed-Int .signum (NegSuc _) = NegSuc 0

  Integral-Int : Integral Int
  Integral-Int .div x y = intDiv x y
  Integral-Int .mod x y = intMod x y
