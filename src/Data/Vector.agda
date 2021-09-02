{-# OPTIONS --type-in-type #-}

module Data.Vector where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude hiding (map)

open import Data.Foldable
open import Data.List as List using ()
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
-- Elementary functions
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

zipWith : (a -> b -> c) -> Vector n a -> Vector n b -> Vector n c
zipWith _ [] [] = []
zipWith f (x :: xs) (y :: ys) = f x y :: zipWith f xs ys

map : (a -> b) -> Vector n a -> Vector n b
map {n = n} f = zipWith _$_ (replicate n f)

diag : Vector n (Vector n a) -> Vector n a
diag [] = []
diag ((x :: xs) :: xss) = x :: diag (map tail xss)

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

splitAt : (m : Nat) -> Vector (m + n) a -> Pair (Vector m a) (Vector n a)
splitAt 0 xs = ([] , xs)
splitAt (Suc k) (x :: xs) = let (l , r) = splitAt k xs in (x :: l , r)

transpose : Vector n (Vector m a) -> Vector m (Vector n a)
transpose = sequence

zip : Vector n a -> Vector n b -> Vector n (Pair a b)
zip = zipWith _,_

fromList : (xs : List a) -> Vector (length xs) a
fromList [] = []
fromList (x :: xs) = x :: fromList xs

take : (n : Nat) (xs : List a) -> Maybe (Vector n a)
take 0 _ = Just []
take (Suc n) [] = Nothing
take (Suc n) (x :: xs) =
  case take n xs of \ where
    Nothing -> Nothing
    (Just xs') -> Just (x :: xs')

reverse : Vector n a -> Vector n a
reverse {n = n} xs =
  unsafePerform $ fromJust $ take n $ List.reverse (toList xs)
