{-# OPTIONS --type-in-type #-}

module Data.Fin where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Data.Nat as Nat using ()

-------------------------------------------------------------------------------
-- Fin primitives
-------------------------------------------------------------------------------

private
  finToNat : {n : Nat} -> Fin n -> Nat
  finToNat Zero = Zero
  finToNat (Suc n) = Suc (finToNat n)

  natToFin : (m n : Nat) -> Maybe (Fin n)
  natToFin Zero (Suc j) = Just Zero
  natToFin (Suc m) (Suc n) =
    case natToFin m n of \ where
      (Just k') -> Just (Suc k')
      Nothing -> Nothing
  natToFin _ _ = Nothing

  finEquality : {n : Nat} -> Fin n -> Fin n -> Bool
  finEquality Zero Zero = True
  finEquality (Suc n) (Suc m) = finEquality n m
  finEquality _ _ = False

  finLessThan : {n : Nat} -> Fin n -> Fin n -> Bool
  finLessThan _ Zero = False
  finLessThan Zero (Suc _) = True
  finLessThan (Suc n) (Suc m) = finLessThan n m

  finPlus : {n : Nat} -> Fin n -> Fin n -> Fin n
  finPlus {Zero} ()
  finPlus {n@(Suc _)} k m =
    case natToFin (mod (finToNat k + finToNat m) n) n of \ where
      (Just k') -> k'
      Nothing -> undefined

  finNegate : {n : Nat} -> Fin n -> Fin n
  finNegate {n} m =
    case natToFin (n - finToNat m) n of \ where
      (Just k) -> k
      Nothing -> undefined

  finMinus : {n : Nat} -> Fin n -> Fin n -> Fin n
  finMinus k m = finPlus k (finNegate m)

  finTimes : {n : Nat} -> Fin n -> Fin n -> Fin n
  finTimes {Zero} ()
  finTimes {n@(Suc _)} k m =
    case natToFin (mod (finToNat k * finToNat m) n) n of \ where
      (Just k') -> k'
      Nothing -> undefined

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

instance
  Eq-Fin : {n : Nat} -> Eq (Fin n)
  Eq-Fin ._==_ = finEquality

  Ord-Fin : {n : Nat} -> Ord (Fin n)
  Ord-Fin .compare m n =
    if m == n then EQ
    else if finLessThan m n then LT
    else GT

  FromNat-Fin : {n : Nat} -> FromNat (Fin (Suc n))
  FromNat-Fin {n} .FromNatConstraint m = Assert (m <= n)
  FromNat-Fin {n} .fromNat m {{p}} = go m n {p}
    where
      go : (m n : Nat) {_ : Assert $ m <= n} -> Fin (Suc n)
      go Zero _ = Zero
      go (Suc m) (Suc n) {p} = Suc (go m n {p})

  ToNat-Fin : {n : Nat} -> ToNat (Fin n)
  ToNat-Fin .ToNatConstraint _ = Unit
  ToNat-Fin .toNat n = finToNat n

  Num-Fin : {n : Nat} -> Num (Fin (Suc n))
  Num-Fin .nonzero Zero = False
  Num-Fin .nonzero _ = True
  Num-Fin ._+_ = finPlus
  Num-Fin ._-_ = finMinus
  Num-Fin ._*_ = finTimes
