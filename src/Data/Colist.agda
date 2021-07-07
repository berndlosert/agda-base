{-# OPTIONS --type-in-type --sized-types #-}

module Data.Colist where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Data.Size

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    i : Size
    a : Type

-------------------------------------------------------------------------------
-- Colist
-------------------------------------------------------------------------------

data Colist (i : Size) (a : Type) : Type where
  [] : Colist i a
  _::_ : a -> Thunk i (\ j -> Colist j a) -> Colist i a

instance
  Semigroup-Colist : Semigroup (Colist i a)
  Semigroup-Colist ._<>_ [] ys = []
  Semigroup-Colist ._<>_ (x :: xs) ys = x :: \ where .force -> (xs .force <> ys)

  Monoid-Colist : Monoid (Colist i a)
  Monoid-Colist .neutral = []
