{-# OPTIONS --type-in-type #-}

module Data.Functor.Identity where

open import Prelude

private
  variable
    A : Set

record Identity (A : Set) : Set where
  constructor Identity:
  field
    run : A

instance
  Eq:Identity : {{_ : Eq A}} -> Eq (Identity A)
  Eq:Identity ._==_ (Identity: x) (Identity: y) = x == y

  Ord:Identity : {{_ : Ord A}} -> Ord (Identity A)
  Ord:Identity ._<_ (Identity: x) (Identity: y) = x < y

  Functor:Identity : Functor Identity
  Functor:Identity .map f (Identity: a) = Identity: (f a)

  Applicative:Identity : Applicative Identity
  Applicative:Identity = \ where
    .pure -> Identity:
    ._<*>_ (Identity: f) x -> map f x

  Monad:Identity : Monad Identity
  Monad:Identity ._>>=_ (Identity: a) k = k a


