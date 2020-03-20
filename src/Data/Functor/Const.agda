{-# OPTIONS --type-in-type #-}

module Data.Functor.Const where

open import Data.Functor.Contravariant
open import Prelude

private
  variable
    A B : Set

record Const (A B : Set) : Set where
  constructor Const:
  field
    get : A

instance
  eqConst : {{_ : Eq A}} -> Eq (Const A B)
  eqConst ._==_ (Const: x) (Const: y) = x == y

  ordConst : {{_ : Ord A}} -> Ord (Const A B)
  ordConst ._<_ (Const: x) (Const: y) = x < y

  functorConst : Functor (Const A)
  functorConst .map f (Const: a) = Const: a

  contravariantConst : Contravariant (Const A)
  contravariantConst .contramap f (Const: a) = Const: a

  applicativeConst : {{_ : Monoid A}} -> Applicative (Const A)
  applicativeConst = \ where
    .pure x -> Const: mempty
    ._<*>_ (Const: x) (Const: y) -> Const: (x <> y)
