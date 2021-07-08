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

take : Nat -> Colist SizeInf a -> List a
take _ [] = []
take 0 _ =  []
take (Suc n) (x :: xs) = x :: take n (force xs)

instance
  Semigroup-Colist : Semigroup (Colist i a)
  Semigroup-Colist ._<>_ [] ys = []
  Semigroup-Colist ._<>_ (x :: xs) ys = x :: \ where .force -> (xs .force <> ys)

  Monoid-Colist : Monoid (Colist i a)
  Monoid-Colist .neutral = []
