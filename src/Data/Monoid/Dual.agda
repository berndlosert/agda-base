{-# OPTIONS --type-in-type #-}

module Data.Monoid.Dual where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

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
  constructor Dual:
  field getDual : a

open Dual public

instance
  Semigroup-Dual : {{_ : Semigroup a}} -> Semigroup (Dual a)
  Semigroup-Dual ._<>_ (Dual: x) (Dual: y) = Dual: (y <> x)

  Monoid-Dual : {{_ : Monoid a}} -> Monoid (Dual a)
  Monoid-Dual .mempty = Dual: mempty

  Functor-Dual : Functor Dual
  Functor-Dual .map f = Dual: <<< f <<< getDual

  Applicative-Dual : Applicative Dual
  Applicative-Dual .pure = Dual:
  Applicative-Dual ._<*>_ (Dual: f) (Dual: x) = Dual: (f x)

  Monad-Dual : Monad Dual
  Monad-Dual ._>>=_ (Dual: x) k = k x

  Show-Dual : {{_ : Show a}} -> Show (Dual a)
  Show-Dual .showsPrec d (Dual: x) = showParen (d > appPrec)
    (showString "Show: " <<< showsPrec appPrec+1 x)
