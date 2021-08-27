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
-- Functions
-----------------------------------------------------------------------------------------

applyN : (a -> a) -> Nat -> a -> a
applyN _ 0 x = x
applyN f (Suc n) x = f (applyN f n x)

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

  Validation-Positive-Nat : Validation Positive Nat
  Validation-Positive-Nat .validate _ 0 = False
  Validation-Positive-Nat .validate _ _ = True

  Validation-Nonzero-Nat : Validation Nonzero Nat
  Validation-Nonzero-Nat .validate _ = validate Positive

  Num-Nat : Num Nat
  Num-Nat ._+_ = primNatPlus
  Num-Nat ._-_ = primNatMinus
  Num-Nat ._*_ = primNatTimes

  Integral-Nat : Integral Nat
  Integral-Nat .div m (Suc n) = primNatDivAux 0 n m n
  Integral-Nat .div m 0 = undefined
  Integral-Nat .mod m (Suc n) = primNatModAux 0 n m n
  Integral-Nat .mod m 0 = undefined
