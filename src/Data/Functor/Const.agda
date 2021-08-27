{-# OPTIONS --type-in-type #-}

module Data.Functor.Const where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Data.Foldable
open import String.Show

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
  Eq-Const ._==_ x y = getConst x == getConst y

  Ord-Const : {{Ord a}} -> Ord (Const a b)
  Ord-Const .compare x y = compare (getConst x) (getConst y)

  Semigroup-Const : {{Semigroup a}} -> Semigroup (Const a b)
  Semigroup-Const ._<>_ x y = Const: (getConst x <> getConst y)

  Monoid-Const : {{Monoid a}} -> Monoid (Const a b)
  Monoid-Const .neutral = Const: neutral

  Foldable-Const : Foldable (Const a)
  Foldable-Const .foldr _ z _ = z

  Functor-Const : Functor (Const a)
  Functor-Const .map _ = Const: <<< getConst

  Bifunctor-Const : Bifunctor Const
  Bifunctor-Const .lmap f x = Const: (f $ getConst x)

  Contravariant-Const : Contravariant (Const a)
  Contravariant-Const .cmap f = Const: <<< getConst

  Applicative-Const : {{Monoid a}} -> Applicative (Const a)
  Applicative-Const .pure _ = Const: neutral
  Applicative-Const ._<*>_ f x = Const: (getConst f <> getConst x)

  Show-Const : {{Show a}} -> Show (Const a b)
  Show-Const .showsPrec d x = showParen (d > appPrec)
    (showString "Const: " <<< showsPrec appPrec+1 (getConst x))
