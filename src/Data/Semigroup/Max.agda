module Data.Semigroup.Max where

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
-- Max
-------------------------------------------------------------------------------

-- For semigroups, monoids, etc. where x <> y = max x y
record Max (a : Set) : Set where
  constructor asMax
  field getMax : a

open Max public

instance
  Semigroup-Max : {{Ord a}} -> Semigroup (Max a)
  Semigroup-Max ._<>_ x y = asMax $ max (getMax x) (getMax y)

  Functor-Max : Functor Max
  Functor-Max .map f = asMax <<< f <<< getMax

  Applicative-Max : Applicative Max
  Applicative-Max .pure = asMax
  Applicative-Max ._<*>_ f x = asMax $ (getMax f) (getMax x)

  Monad-Max : Monad Max
  Monad-Max ._>>=_ m k = k (getMax m)

  Show-Max : {{Show a}} -> Show (Max a)
  Show-Max .showsPrec prec x = showParen (prec > appPrec) $
    showString "asMax " <<< showsPrec appPrec+1 (getMax x)
