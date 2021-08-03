{-# OPTIONS --type-in-type #-}

module Data.Functor.Const where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Data.Foldable

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b : Type

-------------------------------------------------------------------------------
-- Const
-------------------------------------------------------------------------------

record Const (a b : Type) : Type where
  constructor Const:
  field getConst : a

open Const public

instance
  Eq-Const : {{Eq a}} -> Eq (Const a b)
  Eq-Const ._==_ (Const: x) (Const: y) = x == y

  Ord-Const : {{Ord a}} -> Ord (Const a b)
  Ord-Const ._<_ (Const: x) (Const: y) = x < y

  Semigroup-Const : {{Semigroup a}} -> Semigroup (Const a b)
  Semigroup-Const ._<>_ (Const: x) (Const: y) = Const: (x <> y)

  Monoid-Const : {{Monoid a}} -> Monoid (Const a b)
  Monoid-Const .neutral = Const: neutral

  Foldable-Const : Foldable (Const a)
  Foldable-Const .foldr _ z _ = z

  Functor-Const : Functor (Const a)
  Functor-Const .map _ (Const: x) = Const: x

  Bifunctor-Const : Bifunctor Const
  Bifunctor-Const .lmap f (Const: x) = Const: (f x)

  Contravariant-Const : Contravariant (Const a)
  Contravariant-Const .cmap f = Const: <<< getConst

  Applicative-Const : {{Monoid a}} -> Applicative (Const a)
  Applicative-Const .pure _ = Const: neutral
  Applicative-Const ._<*>_ (Const: f) (Const: a) = Const: (f <> a)

  Show-Const : {{Show a}} -> Show (Const a b)
  Show-Const .showsPrec d (Const: x) = showParen (d > appPrec)
    (showString "Const: " <<< showsPrec appPrec+1 x)
