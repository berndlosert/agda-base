{-# OPTIONS --type-in-type #-}

module Data.Function where

open import Data.Functor
open import Data.Monoid
open import Data.Ring
open import Data.Semigroup
open import Data.Semiring
open import Data.Type.Equality
open import Data.Void
open import Prim

private variable A B : Set

record Endo A : Set where
  constructor toEndo
  field fromEndo : A -> A

open Endo public

instance
  semigroupFunction : {{_ : Semigroup B}} -> Semigroup (A -> B)
  semigroupFunction ._<>_ f g = \ a -> f a <> g a

  semigroupEndo : Semigroup (Endo A)
  semigroupEndo ._<>_ g f = toEndo (fromEndo g <<< fromEndo f)

  monoidFunction : {{_ : Monoid B}} -> Monoid (A -> B)
  monoidFunction .mempty = const mempty

  monoidEndo : Monoid (Endo A)
  monoidEndo .mempty = toEndo id

  profunctorFunction : Profunctor Function
  profunctorFunction .dimap f g h = g <<< h <<< f
