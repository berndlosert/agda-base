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
    k : Type
    a a0 a1 a2 a3 : k
    as bs cs : List k

-------------------------------------------------------------------------------
-- Elem
-------------------------------------------------------------------------------

data Elem : k -> List k -> Type where
  here : Elem a (a :: as)
  there : Elem a as -> Elem a (a0 :: as)

elemIndex : (x : a) -> (xs : List a) -> Elem x xs -> Nat
elemIndex _ _ here = 0
elemIndex x (y :: xs) (there elem) = suc (elemIndex x xs elem)

instance
  elem0 : Elem a (a :: as)
  elem0 = here

  elem1 : Elem a (a0 :: a :: as)
  elem1 = there here

  elem2 : Elem a (a0 :: a1 :: a :: as)
  elem2 = there (there here)

  elem3 : Elem a (a0 :: a1 :: a3 :: a :: as)
  elem3 = there (there (there here))

  Uninhabited-Elem : Uninhabited (Elem a [])
  Uninhabited-Elem .uninhabited ()

  Eq-Elem : Eq (Elem a as)
  Eq-Elem ._==_ = \ where
    here here -> true
    (there elem) (there elem') -> elem == elem'
    _ _ -> false

-------------------------------------------------------------------------------
-- Sub
-------------------------------------------------------------------------------

data Sub : List k -> List k -> Type where
  nilSub : Sub [] bs
  consSub : Elem a bs -> Sub as bs -> Sub (a :: as) bs