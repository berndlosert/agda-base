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
    a : Set

-------------------------------------------------------------------------------
-- Colist
-------------------------------------------------------------------------------

data Colist (a : Set) : Set where
  [] : Colist a
  _::_ : a -> Inf (Colist a) -> Colist a

take : Nat -> Colist a -> List a
take _ [] = []
take 0 _ =  []
take (suc n) (x :: xs) = x :: take n (flat xs)

instance
  Semigroup-Colist : Semigroup (Colist a)
  Semigroup-Colist ._<>_ [] ys = []
  Semigroup-Colist ._<>_ (x :: xs) ys = x :: sharp (flat xs <> ys)

  Monoid-Colist : Monoid (Colist a)
  Monoid-Colist .mempty = []
