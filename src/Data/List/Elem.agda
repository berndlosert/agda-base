module Data.List.Elem where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude hiding (pos)

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a a1 a2 a3 : Set
    as bs cs : List Set

-------------------------------------------------------------------------------
-- Elem
-------------------------------------------------------------------------------

record Elem (a : Set) (as : List Set) : Set where
  constructor elemPos
  field pos : Nat

open Elem {{...}} public

instance
  Uninhabited-Elem : Uninhabited (Elem a [])
  Uninhabited-Elem = panic "Elem a [] is uninhabited"

  Elem0 : Elem a (a :: as)
  Elem0 .pos = 0

  Elem1 : Elem a (a1 :: a :: as)
  Elem1 .pos = 1

  Elem2 : Elem a (a1 :: a2 :: a :: as)
  Elem2 .pos = 2

  Elem3 : Elem a (a1 :: a2 :: a3 :: a :: as)
  Elem3 .pos = 3

-------------------------------------------------------------------------------
-- Sub
-------------------------------------------------------------------------------

data Sub : List Set -> List Set -> Set where
  nilSub : Sub [] bs
  consSub : Elem a bs -> Sub as bs -> Sub (a :: as) bs