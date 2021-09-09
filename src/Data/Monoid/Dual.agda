{-# OPTIONS --type-in-type #-}

module Data.Monoid.Dual where

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
-- Dual
-------------------------------------------------------------------------------

-- For dual semigroups, monoids, etc.
record Dual (a : Set) : Set where
  constructor toDual
  field getDual : a

open Dual public

instance
  Semigroup-Dual : {{Semigroup a}} -> Semigroup (Dual a)
  Semigroup-Dual ._<>_ (toDual x) (toDual y) = toDual (y <> x)

  Monoid-Dual : {{Monoid a}} -> Monoid (Dual a)
  Monoid-Dual .neutral = toDual neutral

  Functor-Dual : Functor Dual
  Functor-Dual .map f = toDual <<< f <<< getDual

  Applicative-Dual : Applicative Dual
  Applicative-Dual .pure = toDual
  Applicative-Dual ._<*>_ (toDual f) (toDual x) = toDual (f x)

  Monad-Dual : Monad Dual
  Monad-Dual ._>>=_ (toDual x) k = k x

  Show-Dual : {{Show a}} -> Show (Dual a)
  Show-Dual .showsPrec d (toDual x) = showParen (d > appPrec)
    (showString "toDual " <<< showsPrec appPrec+1 x)
