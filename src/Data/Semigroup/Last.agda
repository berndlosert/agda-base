module Data.Semigroup.Last where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Data.String.Builder
open import Data.String.Show

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
  constructor asLast
  field getLast : a

open Last public

instance
  Semigroup-Last : Semigroup (Last a)
  Semigroup-Last ._<>_ _ y = y

  Monoid-Last : {{Monoid a}} -> Monoid (Last a)
  Monoid-Last .mempty = asLast mempty

  Functor-Last : Functor Last
  Functor-Last .map f = asLast <<< f <<< getLast

  Applicative-Last : Applicative Last
  Applicative-Last .pure = asLast
  Applicative-Last ._<*>_ f x = asLast $ (getLast f) (getLast x)

  Monad-Last : Monad Last
  Monad-Last ._>>=_ m k = k (getLast m)

  Show-Last : {{Show a}} -> Show (Last a)
  Show-Last .show = showDefault
  Show-Last .showsPrec prec x = showParen (prec > appPrec)
    ("asLast " <> showsPrec appPrec+1 (getLast x))
