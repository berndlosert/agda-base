{-# OPTIONS --type-in-type #-}

module Data.Nat where

private variable A : Set

module Nat where
  open import Agda.Builtin.Nat public
    using (Nat; suc; zero)
    renaming (
      _==_ to eq;
      _<_ to lt;
      _+_ to add;
      _-_ to sub;
      _*_ to mul
    )

  open import Agda.Builtin.String public
    renaming (primShowNat to show)

  open import Agda.Builtin.Nat
    using (div-helper; mod-helper)

  open import Prelude
    using (const; Void; Unit)

  natrec : A -> (Nat -> A -> A) -> Nat -> A
  natrec a _ 0 = a
  natrec a h n@(suc n-1) = h n-1 (natrec a h n-1)

  applyN : (A -> A) -> Nat -> A -> A
  applyN f n a = natrec a (const f) n

  Nonzero : Nat -> Set
  Nonzero 0 = Void
  Nonzero (suc _) = Unit

  div : (m n : Nat) {_ : Nonzero n} -> Nat
  div m (suc n) = div-helper 0 n m n

  mod : (m n : Nat) {_ : Nonzero n} -> Nat
  mod m (suc n) = mod-helper 0 n m n

open Nat public
  using (Nat; suc)
  hiding (module Nat)

open import Prelude

instance
  eqNat : Eq Nat
  eqNat ._==_ = Nat.eq

  ordNat : Ord Nat
  ordNat ._<_ = Nat.lt

  semiringNat : Semiring Nat
  semiringNat .zero = 0
  semiringNat .one = 1
  semiringNat ._+_ = Nat.add
  semiringNat ._*_ = Nat.mul

  ringNat : Ring Nat
  ringNat ._-_ = Nat.sub

  numNat : Num Nat
  numNat .Nonzero = Nat.Nonzero
  numNat ._/_ = Nat.div
  numNat ._%_ = Nat.mod
