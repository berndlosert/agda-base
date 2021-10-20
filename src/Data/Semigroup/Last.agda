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
  constructor aLast
  field getLast : a

open Last public

instance
  Semigroup-Last : Semigroup (Last a)
  Semigroup-Last ._<>_ _ y = y

  Monoid-Last : {{Monoid a}} -> Monoid (Last a)
  Monoid-Last .mempty = aLast mempty

  Functor-Last : Functor Last
  Functor-Last .map f = aLast <<< f <<< getLast

  Applicative-Last : Applicative Last
  Applicative-Last .pure = aLast
  Applicative-Last ._<*>_ f x = aLast $ (getLast f) (getLast x)

  Monad-Last : Monad Last
  Monad-Last ._>>=_ m k = k (getLast m)

  Show-Last : {{Show a}} -> Show (Last a)
  Show-Last .showsPrec prec x = showParen (prec > appPrec) $
    showString "aLast " <<< showsPrec appPrec+1 (getLast x)
