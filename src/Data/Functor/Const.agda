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
  Eq:Const : {{_ : Eq A}} -> Eq (Const A B)
  Eq:Const ._==_ (Const: x) (Const: y) = x == y

  Ord:Const : {{_ : Ord A}} -> Ord (Const A B)
  Ord:Const ._<_ (Const: x) (Const: y) = x < y

  Functor:Const : Functor (Const A)
  Functor:Const .map f (Const: a) = Const: a

  Contravariant:Const : Contravariant (Const A)
  Contravariant:Const .contramap f (Const: a) = Const: a

  Applicative:Const : {{_ : Monoid A}} -> Applicative (Const A)
  Applicative:Const = \ where
    .pure x -> Const: mempty
    ._<*>_ (Const: x) (Const: y) -> Const: (x <> y)
