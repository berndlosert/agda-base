{-# OPTIONS --type-in-type #-}

module Data.Nat where

open import Agda.Builtin.Nat public
  using (Nat; suc)

open import Data.Ord
open import Data.Function
open import Data.Semiring
open import Data.Unit
open import Data.Void

private variable A : Set

natrec : A -> (Nat -> A -> A) -> Nat -> A
natrec a _ 0 = a
natrec a h n@(suc n-1) = h n-1 (natrec a h n-1)

applyN : (A -> A) -> Nat -> A -> A
applyN f n a = natrec a (const f) n

monus : Nat -> Nat -> Nat
monus = Agda.Builtin.Nat._-_

instance
  eqNat : Eq Nat
  eqNat ._==_ = Agda.Builtin.Nat._==_

  ordNat : Ord Nat
  ordNat ._<_ = Agda.Builtin.Nat._<_

  semiringNat : Semiring Nat
  semiringNat .zero = 0
  semiringNat .one = 1
  semiringNat ._+_ = Agda.Builtin.Nat._+_
  semiringNat ._*_ = Agda.Builtin.Nat._*_


