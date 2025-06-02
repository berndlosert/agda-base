module Data.List.Sized where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude hiding (map)

open import Data.Monoid.Foldable
open import Data.List as List using ()
open import Data.Traversable

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b c : Type
    m n : Nat

-------------------------------------------------------------------------------
-- ListN
-------------------------------------------------------------------------------

data ListN : Nat -> Type -> Type where
  [] : ListN 0 a
  _::_ : a -> ListN n a -> ListN (suc n) a

-------------------------------------------------------------------------------
-- Elementary functions
-------------------------------------------------------------------------------

head : ListN (suc n) a -> a
head (x :: _) = x

tail : ListN (suc n) a -> ListN n a
tail (_ :: xs) = xs

append : ListN m a -> ListN n a -> ListN (m + n) a
append [] xs = xs
append (x :: xs) ys = x :: append xs ys

replicate : (n : Nat) -> a -> ListN n a
replicate 0 x = []
replicate (suc n) x = x :: replicate n x

zipWith : (a -> b -> c) -> ListN n a -> ListN n b -> ListN n c
zipWith _ [] [] = []
zipWith f (x :: xs) (y :: ys) = f x y :: zipWith f xs ys

map : (a -> b) -> ListN n a -> ListN n b
map {n = n} f = zipWith _$_ (replicate n f)

diag : ListN n (ListN n a) -> ListN n a
diag [] = []
diag ((x :: xs) :: xss) = x :: diag (map tail xss)

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

instance
  Functor-ListN : Functor (ListN n)
  Functor-ListN = record { map = map }

  Applicative-ListN : Applicative (ListN n)
  Applicative-ListN {n} .pure = replicate n
  Applicative-ListN ._<*>_ fs xs = zipWith _$_ fs xs

  Monad-ListN : Monad (ListN n)
  Monad-ListN ._>>=_ m k = diag (map k m)

  Foldable-ListN : Foldable (ListN n)
  Foldable-ListN .foldMap f = \ where
    [] -> mempty
    (x :: xs) -> f x <> foldMap f xs

  Traversable-ListN : Traversable (ListN n)
  Traversable-ListN .traverse f = \ where
    [] -> (| [] |)
    (x :: xs) -> (| f x :: traverse f xs |)

-------------------------------------------------------------------------------
-- More functions
-------------------------------------------------------------------------------

splitAt : (m : Nat) -> ListN (m + n) a -> Tuple (ListN m a) (ListN n a)
splitAt 0 xs = ([] , xs)
splitAt (suc k) (x :: xs) = let (l , r) = splitAt k xs in (x :: l , r)

transpose : ListN n (ListN m a) -> ListN m (ListN n a)
transpose = sequence

zip : ListN n a -> ListN n b -> ListN n (Tuple a b)
zip = zipWith _,_

fromList : (xs : List a) -> ListN (length xs) a
fromList [] = []
fromList (x :: xs) rewrite List.length-cons x xs = x :: fromList xs

take : (n : Nat) (xs : List a) -> Maybe (ListN n a)
take 0 _ = just []
take (suc n) [] = nothing
take (suc n) (x :: xs) =
  case (take n xs) \ where
    nothing -> nothing
    (just ys) -> just (x :: ys)
