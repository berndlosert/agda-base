{-# OPTIONS --type-in-type #-}

module Data.Functor.Identity where

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
    a : Set

-------------------------------------------------------------------------------
-- Identity
-------------------------------------------------------------------------------

record Identity (a : Set) : Set where
  constructor Identity:
  field runIdentity : a

open Identity public

instance
  Eq-Identity : {{_ : Eq a}} -> Eq (Identity a)
  Eq-Identity ._==_ (Identity: x) (Identity: y) = x == y

  Ord-Identity : {{_ : Ord a}} -> Ord (Identity a)
  Ord-Identity ._<_ (Identity: x) (Identity: y) = x < y

  Semigroup-Identity : {{_ : Semigroup a}} -> Semigroup (Identity a)
  Semigroup-Identity ._<>_ (Identity: x) (Identity: y) =
    Identity: (x <> y)

  Monoid-Identity : {{_ : Monoid a}} -> Monoid (Identity a)
  Monoid-Identity .neutral = Identity: neutral

  Foldable-Identity : Foldable Identity
  Foldable-Identity .foldMap f (Identity: x) = f x

  Functor-Identity : Functor Identity
  Functor-Identity .map f = Identity: <<< f <<< runIdentity

  Applicative-Identity : Applicative Identity
  Applicative-Identity .pure = Identity:
  Applicative-Identity ._<*>_ = map <<< runIdentity

  Monad-Identity : Monad Identity
  Monad-Identity ._>>=_ (Identity: x) k = k x

  Show-Identity : {{_ : Show a}} -> Show (Identity a)
  Show-Identity .showsPrec d (Identity: x) = showParen (d > appPrec)
    (showString "Identity: " <<< showsPrec appPrec+1 x)
