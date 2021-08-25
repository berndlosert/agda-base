{-# OPTIONS --type-in-type #-}

module Data.Monoid.Dual where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Data.Nat as Nat using ()
open import String.Show

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a : Type

-------------------------------------------------------------------------------
-- Dual
-------------------------------------------------------------------------------

-- For dual semigroups, monoids, etc.
record Dual (a : Type) : Type where
  constructor Dual:
  field getDual : a

open Dual public

instance
  Semigroup-Dual : {{Semigroup a}} -> Semigroup (Dual a)
  Semigroup-Dual ._<>_ (Dual: x) (Dual: y) = Dual: (y <> x)

  Monoid-Dual : {{Monoid a}} -> Monoid (Dual a)
  Monoid-Dual .neutral = Dual: neutral

  Functor-Dual : Functor Dual
  Functor-Dual .map f = Dual: <<< f <<< getDual

  Applicative-Dual : Applicative Dual
  Applicative-Dual .pure = Dual:
  Applicative-Dual ._<*>_ (Dual: f) (Dual: x) = Dual: (f x)

  Monad-Dual : Monad Dual
  Monad-Dual ._>>=_ (Dual: x) k = k x

  Show-Dual : {{Show a}} -> Show (Dual a)
  Show-Dual .showsPrec d (Dual: x) = showParen (d > appPrec)
    (showString "Dual: " <<< showsPrec appPrec+1 x)
