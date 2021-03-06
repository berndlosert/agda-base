{-# OPTIONS --type-in-type #-}

module Data.Semigroup.First where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a : Type

-------------------------------------------------------------------------------
-- First
-------------------------------------------------------------------------------

-- Semigroup where x <> y = x
record First (a : Type) : Type where
  constructor First:
  field getFirst : a

open First public

instance
  Semigroup-First : Semigroup (First a)
  Semigroup-First ._<>_ x _ = x

  Monoid-First : {{_ : Monoid a}} -> Monoid (First a)
  Monoid-First .neutral = First: neutral

  Functor-First : Functor First
  Functor-First .map f = First: <<< f <<< getFirst

  Applicative-First : Applicative First
  Applicative-First .pure = First:
  Applicative-First ._<*>_ (First: f) (First: x) = First: (f x)

  Monad-First : Monad First
  Monad-First ._>>=_ (First: x) k = k x

  Show-First : {{_ : Show a}} -> Show (First a)
  Show-First .showsPrec d (First: x) = showParen (d > appPrec)
    (showString "First: " <<< showsPrec appPrec+1 x)
