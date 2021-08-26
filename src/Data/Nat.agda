{-# OPTIONS --type-in-type #-}

module Data.Nat where

-----------------------------------------------------------------------------------------
-- Imports
-----------------------------------------------------------------------------------------

open import Prelude

open import Agda.Builtin.Nat
  renaming (_==_ to primNatEquality)
  renaming (_<_ to primNatLessThan)
  renaming (_+_ to primNatPlus)
  renaming (_-_ to primNatMinus)
  renaming (_*_ to primNatTimes)
  renaming (div-helper to primNatDivAux)
  renaming (mod-helper to primNatModAux)

-----------------------------------------------------------------------------------------
-- Variables
-----------------------------------------------------------------------------------------

private
  variable
    a : Type

-----------------------------------------------------------------------------------------
-- Nat primitives
-----------------------------------------------------------------------------------------

applyN : (a -> a) -> Nat -> a -> a
applyN _ 0 x = x
applyN f (Suc n) x = f (applyN f n x)

private
  natDiv : {{Unsafe}} -> Nat -> Nat -> Nat
  natDiv m (Suc n) = primNatDivAux Zero n m n
  natDiv _ _ = undefined

  natMod : {{Unsafe}} -> Nat -> Nat -> Nat
  natMod m (Suc n) = primNatModAux Zero n m n
  natMod _ _ = undefined

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

instance
  Eq-Nat : Eq Nat
  Eq-Nat ._==_ = primNatEquality

  Ord-Nat : Ord Nat
  Ord-Nat .compare m n =
    if m == n then EQ
    else if primNatLessThan m n then LT
    else GT

  FromNat-Nat : FromNat Nat
  FromNat-Nat .FromNatConstraint _ = Unit
  FromNat-Nat .fromNat n = n

  ToNat-Nat : ToNat Nat
  ToNat-Nat .ToNatConstraint _ = Unit
  ToNat-Nat .toNat n = n

  Num-Nat : Num Nat
  Num-Nat .nonzero 0 = False
  Num-Nat .nonzero _ = True
  Num-Nat ._+_ = primNatPlus
  Num-Nat ._-_ = primNatMinus
  Num-Nat ._*_ = primNatTimes

  Integral-Nat : Integral Nat
  Integral-Nat .div x y = unsafePerform natDiv x y
  Integral-Nat .mod x y = unsafePerform natMod x y
