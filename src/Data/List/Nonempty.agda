module Data.List.Nonempty where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Data.Monoid.Foldable
open import Data.Nonempty
open import Data.String.Show

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a : Type

-------------------------------------------------------------------------------
-- List1
-------------------------------------------------------------------------------

data List1 (a : Type) : Type where
  _::_ :  a -> List a -> List1 a

instance
  Eq-List1 : {{Eq a}} -> Eq (List1 a)
  Eq-List1 ._==_ (x :: xs) (y :: ys) = x == y && xs == ys

  Ord-List1 : {{Ord a}} -> Ord (List1 a)
  Ord-List1 ._<_ (x :: xs) (y :: ys) = x < y && xs < ys

  Semigroup-List1 : Semigroup (List1 a)
  Semigroup-List1 ._<>_ (x :: xs) (y :: ys) = x :: (xs <> y :: ys)

  Foldable-List1 : Foldable List1
  Foldable-List1 .foldMap f = \ where
    (x :: []) -> f x
    (x :: (y :: ys)) -> f x <> foldMap {List} f (y :: ys)

  Functor-List1 : Functor List1
  Functor-List1 .map f (x :: xs) = f x :: map f xs  

  Nonemptiness-List : Nonemptiness (List a)
  Nonemptiness-List {a} .Nonempty = List1 a
  Nonemptiness-List .nonempty (x :: xs) = just (x :: xs)  
  Nonemptiness-List .nonempty [] = nothing

  Show-List1 : {{Show a}} -> Show (List1 a)
  Show-List1 .show = showDefault
  Show-List1 .showsPrec prec (x :: xs) = showParen (prec > appPrec)
    (showsPrec appPrec+1 x <> " :: " <> showsPrec 0 xs)  