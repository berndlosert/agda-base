{-# OPTIONS --type-in-type #-}

module Data.Nat where

import Agda.Builtin.Nat
open import Data.Eq
open import Data.Euclidean
open import Data.Ord
open import Data.Semiring
open import Prim

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
  semiringNat .Nonzero 0 = Void
  semiringNat .Nonzero (suc _) = Unit

  euclideanNat : Euclidean Nat
  euclideanNat .degree n = n
  euclideanNat .quot m 0 = 0 -- unreachable
  euclideanNat .quot m (suc n) = Agda.Builtin.Nat.div-helper 0 n m n
  euclideanNat .mod m 0 = 0 -- unreachable
  euclideanNat .mod m (suc n) = Agda.Builtin.Nat.mod-helper 0 n m n
