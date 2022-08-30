module Data.Semigroup.Min where

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
-- Min
-------------------------------------------------------------------------------

-- For semigroups, monoids, etc. where x <> y = min x y
record Min (a : Set) : Set where
  constructor asMin
  field getMin : a

open Min public

instance
  Semigroup-Min : {{Ord a}} -> Semigroup (Min a)
  Semigroup-Min ._<>_ x y = asMin $ min (getMin x) (getMin y)

  Functor-Min : Functor Min
  Functor-Min .map f = asMin <<< f <<< getMin

  Applicative-Min : Applicative Min
  Applicative-Min .pure = asMin
  Applicative-Min ._<*>_ f x = asMin $ (getMin f) (getMin x)

  Monad-Min : Monad Min
  Monad-Min ._>>=_ m k = k (getMin m)

  Show-Min : {{Show a}} -> Show (Min a)
  Show-Min .showsPrec prec x = showParen (prec > appPrec) $
    showString "asMin " <<< showsPrec appPrec+1 (getMin x)
