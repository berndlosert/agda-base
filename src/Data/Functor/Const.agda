{-# OPTIONS --type-in-type #-}

module Data.Functor.Const where

open import Data.Functor.Contravariant
open import Prelude

private variable A B : Set

record Const (A B : Set) : Set where
  constructor value
  field get : A

instance
  eqConst : {{_ : Eq A}} -> Eq (Const A B)
  eqConst ._==_ (value x) (value y) = x == y

  ordConst : {{_ : Ord A}} -> Ord (Const A B)
  ordConst ._<_ (value x) (value y) = x < y

  functorConst : Functor (Const A)
  functorConst .map f (value a) = value a

  contravariantConst : Contravariant (Const A)
  contravariantConst .contramap f (value a) = value a

  applicativeConst : {{_ : Monoid A}} -> Applicative (Const A)
  applicativeConst = \ where
    .pure x -> value empty
    ._<*>_ (value x) (value y) -> value (x <> y)
