{-# OPTIONS --type-in-type #-}

module Data.Functor.Identity where

open import Prelude

record Identity (X : Set) : Set where
  constructor Identity:
  field
    run : X

instance
  Eq:Identity : forall {X} {{_ : Eq X}} -> Eq (Identity X)
  Eq:Identity ._==_ (Identity: x) (Identity: x') = x == x'

  Ord:Identity : forall {X} {{_ : Ord X}} -> Ord (Identity X)
  Ord:Identity ._<_ (Identity: x) (Identity: x') = x < x'

  Functor:Identity : Functor Identity
  Functor:Identity .map f (Identity: x) = Identity: (f x)

  Monad:Identity : Monad Identity
  Monad:Identity = \ where
    .return x -> Identity: x
    .extend f (Identity: x) -> f x

  Applicative:Identity : Applicative Identity
  Applicative:Identity = \ where
    .pure -> return
    ._<*>_ -> ap
