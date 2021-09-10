{-# OPTIONS --type-in-type #-}

module Data.Semigroup.First where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import String.Show

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a : Set

-------------------------------------------------------------------------------
-- First
-------------------------------------------------------------------------------

-- Semigroup where x <> y = x
record First (a : Set) : Set where
  constructor toFirst
  field getFirst : a

open First public

instance
  Semigroup-First : Semigroup (First a)
  Semigroup-First ._<>_ x _ = x

  Monoid-First : {{Monoid a}} -> Monoid (First a)
  Monoid-First .mempty = toFirst mempty

  Functor-First : Functor First
  Functor-First .map f = toFirst <<< f <<< getFirst

  Applicative-First : Applicative First
  Applicative-First .pure = toFirst
  Applicative-First ._<*>_ f x = toFirst $ (getFirst f) (getFirst x)

  Monad-First : Monad First
  Monad-First ._>>=_ m k = k (getFirst m)

  Show-First : {{Show a}} -> Show (First a)
  Show-First .showsPrec d x = showParen (d > appPrec) $
    showString "toFirst " <<< showsPrec appPrec+1 (getFirst x)
