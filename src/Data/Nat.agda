{-# OPTIONS --type-in-type #-}

module Data.Nat where

open import Agda.Builtin.Nat public using (Nat; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Division public using (Division; Nonzero; _/_; _%_)
open import Data.Eq public using (Eq; _==_; _/=_)
open import Data.Function using (const)
open import Data.Ord using (Ord)
open import Data.Ord public using (compare; LT; EQ; GT)
open import Data.Ord public using (_<_; _<=_; _>_; _>=_)
open import Data.Ord public using (min; max; comparing)
open import Data.Ring using (Ring)
open import Data.Ring public using (-_; _-_)
open import Data.Semiring using (Semiring; zero; one)
open import Data.Semiring public using (_+_; _*_)
open import Data.Unit using (Unit)
open import Data.Void using (Void)

private variable A : Set

natrec : A -> (Nat -> A -> A) -> Nat -> A
natrec a _ 0 = a
natrec a h n@(suc n-1) = h n-1 (natrec a h n-1)

applyN : (A -> A) -> Nat -> A -> A
applyN f n a = natrec a (const f) n

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

  ringNat : Ring Nat
  ringNat .-_ n = 0 - n
  ringNat ._-_ = Agda.Builtin.Nat._-_

  divisionNat : Division Nat
  divisionNat .Nonzero = \ where
    0 -> Void
    (suc _) -> Unit
  divisionNat ._/_ m (suc n) = Agda.Builtin.Nat.div-helper 0 n m n
  divisionNat ._%_ m (suc n) = Agda.Builtin.Nat.mod-helper 0 n m n
