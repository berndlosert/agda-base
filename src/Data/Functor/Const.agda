module Data.Functor.Const where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Data.Bifunctor
open import Data.Foldable
open import Data.Functor.Contravariant
open import Data.String.Show

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a k : Set
    b : k

-------------------------------------------------------------------------------
-- Const
-------------------------------------------------------------------------------

record Const (a : Set) (b : k) : Set where
  constructor asConst
  field getConst : a

open Const public

instance
  Eq-Const : {{Eq a}} -> Eq (Const a b)
  Eq-Const ._==_ = _==_ on getConst

  Ord-Const : {{Ord a}} -> Ord (Const a b)
  Ord-Const ._<_ = _<_ on getConst

  Semigroup-Const : {{Semigroup a}} -> Semigroup (Const a b)
  Semigroup-Const ._<>_ x y = asConst (getConst x <> getConst y)

  Monoid-Const : {{Monoid a}} -> Monoid (Const a b)
  Monoid-Const .mempty = asConst mempty

  Foldable-Const : Foldable (Const a)
  Foldable-Const .foldr _ init _ = init

  Functor-Const : Functor (Const a)
  Functor-Const .map _ = asConst <<< getConst

  Bifunctor-Const : Bifunctor Const
  Bifunctor-Const .lmap f x = asConst (f $ getConst x)

  Contravariant-Const : Contravariant (Const a)
  Contravariant-Const .cmap f = asConst <<< getConst

  Applicative-Const : {{Monoid a}} -> Applicative (Const a)
  Applicative-Const .pure _ = asConst mempty
  Applicative-Const ._<*>_ f x = asConst (getConst f <> getConst x)

  Show-Const : {{Show a}} -> Show (Const a b)
  Show-Const .show = showDefault
  Show-Const .showsPrec prec x = showsUnaryWith showsPrec "Const" prec x
