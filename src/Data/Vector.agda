{-# OPTIONS --type-in-type #-}

module Data.Vector where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude hiding (map)

open import Data.Foldable
open import Data.Traversable

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b c : Set
    m n : Nat

-------------------------------------------------------------------------------
-- Vector
-------------------------------------------------------------------------------

data Vector : Nat -> Set -> Set where
  [] : Vector Zero a
  _::_ : a -> Vector n a -> Vector (Suc n) a

-------------------------------------------------------------------------------
-- Some elementary functions
-------------------------------------------------------------------------------

head : Vector (Suc n) a -> a
head (x :: _) = x

tail : Vector (Suc n) a -> Vector n a
tail (_ :: xs) = xs

append : Vector m a -> Vector n a -> Vector (m + n) a
append [] xs = xs
append (x :: xs) ys = x :: append xs ys

replicate : (n : Nat) -> a -> Vector n a
replicate Zero x = []
replicate (Suc n) x = x :: replicate n x

map : (a -> b) -> Vector n a -> Vector n b
map f [] = []
map f (x :: xs) = f x :: map f xs

diag : Vector n (Vector n a) -> Vector n a
diag [] = []
diag ((x :: xs) :: xss) = x :: diag (map tail xss)

zipWith : (a -> b -> c) -> Vector n a -> Vector n b -> Vector n c
zipWith f = \ where
  [] [] -> []
  (x :: xs) (y :: ys) -> f x y :: zipWith f xs ys

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

instance
  Functor-Vector : Functor (Vector n)
  Functor-Vector = record { map = map }

  Applicative-Vector : Applicative (Vector n)
  Applicative-Vector {n} .pure = replicate n
  Applicative-Vector ._<*>_ fs xs = zipWith _$_ fs xs

  Monad-Vector : Monad (Vector n)
  Monad-Vector ._>>=_ m k = diag (map k m)

  Foldable-Vector : Foldable (Vector n)
  Foldable-Vector .foldr f z = \ where
    [] -> z
    (x :: xs) -> f x (foldr f z xs)

  Traversable-Vector : Traversable (Vector n)
  Traversable-Vector .traverse f = \ where
    [] -> (| [] |)
    (x :: xs) -> (| _::_ (f x) (traverse f xs) |)

-------------------------------------------------------------------------------
-- More functions
-------------------------------------------------------------------------------

splitAt : (m : Nat) -> Vector (m + n) a -> Vector m a * Vector n a
splitAt 0 xs = ([] , xs)
splitAt (Suc k) (x :: xs) with (splitAt k xs)
... | (l , r) = (x :: l , r)

transpose : Vector n (Vector m a) -> Vector m (Vector n a)
transpose = sequence

zip : Vector n a -> Vector n b -> Vector n (a * b)
zip = zipWith _,_
