{-# OPTIONS --type-in-type #-}

module Data.Functor.Const where

open import Data.Functor.Contravariant
open import Prelude

private variable A B : Set

record Const (A B : Set) : Set where
  constructor toConst
  field fromConst : A
open Const public

instance
  eqConst : {{_ : Eq A}} -> Eq (Const A B)
  eqConst ._==_ = on _==_ fromConst

  ordConst : {{_ : Ord A}} -> Ord (Const A B)
  ordConst ._<_ = on _<_ fromConst

  semigroupConst : {{_ : Semigroup A}} -> Semigroup (Const A B)
  semigroupConst ._<>_ x y = toConst $ fromConst x <> fromConst y

  monoidConst : {{_ : Monoid A}} -> Monoid (Const A B)
  monoidConst .mempty = toConst mempty

  functorConst : Functor (Const A)
  functorConst .map f = toConst <<< fromConst

  contravariantConst : Contravariant (Const A)
  contravariantConst .contramap f = toConst <<< fromConst

  applicativeConst : {{_ : Monoid A}} -> Applicative (Const A)
  applicativeConst = \ where
    .pure x -> toConst mempty
    ._<*>_ f x -> toConst $ fromConst f <> fromConst x


