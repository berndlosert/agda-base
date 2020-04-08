{-# OPTIONS --type-in-type #-}

module Data.Nat where

--open import Data.Bool
--open import Data.Either
open import Data.Ord
open import Data.Function
open import Data.Num
open import Data.Unit
open import Data.Void

private variable A : Set

import Agda.Builtin.Nat as Builtin
open Builtin using (Nat; suc) public

natrec : A -> (Nat -> A -> A) -> Nat -> A
natrec a _ 0 = a
natrec a h n@(suc n-1) = h n-1 (natrec a h n-1)

applyN : (A -> A) -> Nat -> A -> A
applyN f n a = natrec a (const f) n

instance
  eqNat : Eq Nat
  eqNat ._==_ = Builtin._==_

  ordNat : Ord Nat
  ordNat ._<_ = Builtin._<_

  semiringNat : Semiring Nat
  semiringNat .zero = 0
  semiringNat .one = 1
  semiringNat ._+_ = Builtin._+_
  semiringNat ._*_ = Builtin._*_

  ringNat : Ring Nat
  ringNat ._-_ = Builtin._-_

  numNat : Num Nat
  numNat .Nonzero 0 = Void
  numNat .Nonzero (suc _) = Unit
  numNat ._/_ m (suc n) = Builtin.div-helper 0 n m n
  numNat ._%_ m (suc n) = Builtin.mod-helper 0 n m n
