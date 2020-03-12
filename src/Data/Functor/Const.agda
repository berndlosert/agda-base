{-# OPTIONS --type-in-type #-}

module Data.Functor.Const where

open import Prelude

record Const (X Y : Set) : Set where
  constructor Const:
  field
    get : X

instance
  Eq:Const : forall {X Y} {{_ : Eq X}} -> Eq (Const X Y)
  Eq:Const ._==_ (Const: x) (Const: x') = x == x'

  Ord:Const : forall {X Y} {{_ : Ord X}} -> Ord (Const X Y)
  Ord:Const ._<_ (Const: x) (Const: x') = x < x'

  Functor:Const : forall {X} -> Functor (Const X)
  Functor:Const .map f (Const: x) = Const: x

  Contravariant:Const : forall {X} -> Contravariant (Const X)
  Contravariant:Const .map f (Const: x) = Const: x

  Applicative:Const : forall {X} {{_ : Monoid X}} -> Applicative (Const X)
  Applicative:Const = \ where
    .pure x -> Const: mempty
    ._<*>_ (Const: x) (Const: x') -> Const: (x <> x')
