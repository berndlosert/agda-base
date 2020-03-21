{-# OPTIONS --type-in-type #-}

module Data.Functor.Const where

open import Data.Functor.Contravariant
open import Prelude

private variable A B : Set

record Const (A B : Set) : Set where
  constructor const:
  field getConst : A
open Const public

instance
  eqConst : {{_ : Eq A}} -> Eq (Const A B)
  eqConst ._==_ (const: x) (const: y) = x == y

  ordConst : {{_ : Ord A}} -> Ord (Const A B)
  ordConst ._<_ (const: x) (const: y) = x < y

  functorConst : Functor (Const A)
  functorConst .map f (const: a) = const: a

  contravariantConst : Contravariant (Const A)
  contravariantConst .contramap f (const: a) = const: a

  applicativeConst : {{_ : Monoid A}} -> Applicative (Const A)
  applicativeConst = \ where
    .pure x -> const: empty
    ._<*>_ (const: x) (const: y) -> const: (x <> y)
