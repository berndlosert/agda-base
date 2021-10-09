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
  constructor toLast
  field getLast : a

open Last public

instance
  Semigroup-Last : Semigroup (Last a)
  Semigroup-Last ._<>_ _ y = y

  Monoid-Last : {{Monoid a}} -> Monoid (Last a)
  Monoid-Last .mempty = toLast mempty

  Functor-Last : Functor Last
  Functor-Last .map f = toLast <<< f <<< getLast

  Applicative-Last : Applicative Last
  Applicative-Last .pure = toLast
  Applicative-Last ._<*>_ f x = toLast $ (getLast f) (getLast x)

  Monad-Last : Monad Last
  Monad-Last ._>>=_ m k = k (getLast m)

  Show-Last : {{Show a}} -> Show (Last a)
  Show-Last .showsPrec d x = showParen (d > appPrec) $
    showString "toLast " <<< showsPrec appPrec+1 (getLast x)
