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
    a b : Set

-------------------------------------------------------------------------------
-- Const
-------------------------------------------------------------------------------

record Const (a b : Set) : Set where
  constructor aConst
  field getConst : a

open Const public

instance
  Eq-Const : {{Eq a}} -> Eq (Const a b)
  Eq-Const ._==_ = _==_ on getConst

  Ord-Const : {{Ord a}} -> Ord (Const a b)
  Ord-Const ._<_ = _<_ on getConst

  Semigroup-Const : {{Semigroup a}} -> Semigroup (Const a b)
  Semigroup-Const ._<>_ x y = aConst (getConst x <> getConst y)

  Monoid-Const : {{Monoid a}} -> Monoid (Const a b)
  Monoid-Const .mempty = aConst mempty

  Foldable-Const : Foldable (Const a)
  Foldable-Const .foldr _ init _ = init

  Functor-Const : Functor (Const a)
  Functor-Const .map _ = aConst <<< getConst

  Bifunctor-Const : Bifunctor Const
  Bifunctor-Const .lmap f x = aConst (f $ getConst x)

  Contravariant-Const : Contravariant (Const a)
  Contravariant-Const .cmap f = aConst <<< getConst

  Applicative-Const : {{Monoid a}} -> Applicative (Const a)
  Applicative-Const .pure _ = aConst mempty
  Applicative-Const ._<*>_ f x = aConst (getConst f <> getConst x)

  Show-Const : {{Show a}} -> Show (Const a b)
  Show-Const .showsPrec prec x = showParen (prec > appPrec)
    (showString "aConst " <<< showsPrec appPrec+1 (getConst x))
