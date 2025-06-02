module Data.Semigroup.First where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Data.String.Show

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
  constructor asFirst
  field getFirst : a

open First public

instance
  Semigroup-First : Semigroup (First a)
  Semigroup-First ._<>_ x _ = x

  Monoid-First : {{Monoid a}} -> Monoid (First a)
  Monoid-First .mempty = asFirst mempty

  Functor-First : Functor First
  Functor-First .map f = asFirst <<< f <<< getFirst

  Applicative-First : Applicative First
  Applicative-First .pure = asFirst
  Applicative-First ._<*>_ f x = asFirst ((getFirst f) (getFirst x))

  Monad-First : Monad First
  Monad-First ._>>=_ m k = k (getFirst m)

  Show-First : {{Show a}} -> Show (First a)
  Show-First .show = showDefault
  Show-First .showsPrec prec (asFirst x) =
    showsUnaryWith showsPrec "asFirst" prec x
