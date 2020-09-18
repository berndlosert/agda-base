{-# OPTIONS --type-in-type #-}

module Data.Colist where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    i : Size
    a : Set

-------------------------------------------------------------------------------
-- Colist
-------------------------------------------------------------------------------

data Colist (a : Set) (i : Size) : Set where
  [] : Colist a i
  _::_ : a -> Thunk (Colist a) i -> Colist a i

instance
  Semigroup-Colist : Semigroup (Colist a i)
  Semigroup-Colist ._<>_ [] ys = []
  Semigroup-Colist ._<>_ (x :: xs) ys = x :: \ where .force -> (xs .force <> ys)

  Monoid-Colist : Monoid (Colist a i)
  Monoid-Colist .neutral = []

  IsBuildable-Colist : IsBuildable (Colist a i) a
  IsBuildable-Colist .singleton a = a :: \ where .force -> []
