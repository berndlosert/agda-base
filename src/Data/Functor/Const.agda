module Data.Functor.Const where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b : Type

-------------------------------------------------------------------------------
-- Const
-------------------------------------------------------------------------------

record Const (a b : Type) : Type where
  constructor asConst
  field getConst : a

open Const public

instance
  Eq-Const : {{Eq a}} -> Eq (Const a b)
  Eq-Const ._==_ x y = getConst x == getConst y

  Ord-Const : {{Ord a}} -> Ord (Const a b)
  Ord-Const ._<_ x y = getConst x < getConst y
