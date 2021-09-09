{-# OPTIONS --type-in-type #-}

module Data.Semigroup.Max where

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
-- Max
-------------------------------------------------------------------------------

-- For semigroups, monoids, etc. where x <> y = max x y
record Max (a : Set) : Set where
  constructor toMax
  field getMax : a

open Max public

instance
  Semigroup-Max : {{Ord a}} -> Semigroup (Max a)
  Semigroup-Max ._<>_ x y = toMax $ max (getMax x) (getMax y)

  Functor-Max : Functor Max
  Functor-Max .map f = toMax <<< f <<< getMax

  Applicative-Max : Applicative Max
  Applicative-Max .pure = toMax
  Applicative-Max ._<*>_ f x = toMax $ (getMax f) (getMax x)

  Monad-Max : Monad Max
  Monad-Max ._>>=_ m k = k (getMax m)

  Show-Max : {{Show a}} -> Show (Max a)
  Show-Max .showsPrec d x = showParen (d > appPrec) $
    showString "toMax " <<< showsPrec appPrec+1 (getMax x)
