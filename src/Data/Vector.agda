module Data.Vector where

open import Prelude

private
  variable
    a : Set
    m n : Nat

data Vector (a : Set) : Nat -> Set where
  [] : Vector a 0
  _::_ : forall {n} -> a -> Vector a n -> Vector a (Suc n)

append : Vector a m -> Vector a n -> Vector a (m + n)
append [] as = as
append (a :: as) as' = a :: append as as'

splitAt : (m : Nat) -> Vector a (m + n) -> Vector a m * Vector a n
splitAt 0 as = ([] , as)
splitAt (Suc k) (a :: as) with (splitAt k as)
... | (l , r) = (a :: l , r)
