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
  Semigroup-Max ._<>_ (toMax x) (toMax y) = toMax (max x y)

  Functor-Max : Functor Max
  Functor-Max .map f = toMax <<< f <<< getMax

  Applicative-Max : Applicative Max
  Applicative-Max .pure = toMax
  Applicative-Max ._<*>_ (toMax f) (toMax x) = toMax (f x)

  Monad-Max : Monad Max
  Monad-Max ._>>=_ (toMax x) k = k x

  Show-Max : {{Show a}} -> Show (Max a)
  Show-Max .showsPrec d (toMax x) = showParen (d > appPrec)
    (showString "toMax " <<< showsPrec appPrec+1 x)
