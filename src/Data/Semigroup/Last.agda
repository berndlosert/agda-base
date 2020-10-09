{-# OPTIONS --type-in-type #-}

module Data.Semigroup.Last where

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
-- Last
-------------------------------------------------------------------------------

-- Semigroup where x <> y = y
record Last (a : Set) : Set where
  constructor Last:
  field getLast : a

open Last public

instance
  Semigroup-Last : Semigroup (Last a)
  Semigroup-Last ._<>_ _ y = y

  Monoid-Last : {{_ : Monoid a}} -> Monoid (Last a)
  Monoid-Last .mempty = Last: mempty

  Functor-Last : Functor Last
  Functor-Last .map f = Last: <<< f <<< getLast

  Applicative-Last : Applicative Last
  Applicative-Last .pure = Last:
  Applicative-Last ._<*>_ (Last: f) (Last: x) = Last: (f x)

  Monad-Last : Monad Last
  Monad-Last ._>>=_ (Last: x) k = k x

  Show-Last : {{_ : Show a}} -> Show (Last a)
  Show-Last .showsPrec d (Last: x) = showParen (d > appPrec)
    (showString "Last: " <<< showsPrec appPrec+1 x)
