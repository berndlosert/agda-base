{-# OPTIONS --type-in-type #-}

module Data.Vector where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Data.Foldable
open import Data.Traversable

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a : Set
    m n : Nat

-------------------------------------------------------------------------------
-- Vector
-------------------------------------------------------------------------------

data Vector : Nat -> Set -> Set where
  [] : Vector 0 a
  _::_ : a -> Vector n a -> Vector (Suc n) a

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

instance
  Functor-Vector : Functor (Vector n)
  Functor-Vector .map f = \ where
    [] -> []
    (x :: xs) -> f x :: map f xs

  Applicative-Vector : Applicative (Vector n)
  Applicative-Vector {n = Zero} .pure _ = []
  Applicative-Vector {n = Suc _} .pure x = x :: pure x
  Applicative-Vector ._<*>_ [] [] = []
  Applicative-Vector ._<*>_ (f :: fs) (x :: xs) = f x :: (fs <*> xs)

  Foldable-Vector : Foldable (Vector n)
  Foldable-Vector .foldr f z = \ where
    [] -> z
    (x :: xs) -> f x (foldr f z xs)

  Traversable-Vector : Traversable (Vector n)
  Traversable-Vector .traverse f [] = (| [] |)
  Traversable-Vector .traverse f (x :: xs) = (| _::_ (f x) (traverse f xs) |)

-------------------------------------------------------------------------------
-- Functions
-------------------------------------------------------------------------------

tail : Vector (Suc n) a -> Vector n a
tail (x :: xs) = xs

append : Vector m a -> Vector n a -> Vector (m + n) a
append [] xs = xs
append (x :: xs) ys = x :: append xs ys

splitAt : (m : Nat) -> Vector (m + n) a -> Vector m a * Vector n a
splitAt 0 xs = ([] , xs)
splitAt (Suc k) (x :: xs) with (splitAt k xs)
... | (l , r) = (x :: l , r)

--transpose : Vector n (Vector m a) -> Vector m (Vector n a)
--transpose = traverse id
