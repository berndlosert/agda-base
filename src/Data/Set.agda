module Data.Set where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude hiding (map)

open import Data.Monoid.Foldable
open import Data.String.Show
open import Data.Tree.Balanced.TwoThree as Tree using (Tree)
open import Data.Traversable

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b : Type
    f : Type -> Type

-------------------------------------------------------------------------------
-- Set
-------------------------------------------------------------------------------

abstract
  Set : Type -> Type
  Set a = Tree a

-------------------------------------------------------------------------------
-- Basic operations
-------------------------------------------------------------------------------

  empty : Set a
  empty = Tree.empty

  singleton : a -> Set a
  singleton = Tree.singleton

  elems : Set a -> List a
  elems = toList

  insert : {{Ord a}} -> a -> Set a -> Set a
  insert = Tree.insert

  delete : {{Ord a}} -> a -> Set a -> Set a
  delete = Tree.delete

  member : {{Ord a}} -> a -> Set a -> Bool
  member = Tree.member

  union : {{Ord a}} -> Set a -> Set a -> Set a
  union = Tree.merge

  unions : {{Foldable f}} -> {{Ord a}} -> f (Set a) -> Set a
  unions = foldl union empty

  difference : {{Ord a}} -> Set a -> Set a -> Set a
  difference xs ys = foldr Tree.delete xs ys

  intersection : {{Ord a}} -> Set a -> Set a -> Set a
  intersection xs ys = difference xs (difference xs ys)

  fromList : {{Ord a}} -> List a -> Set a
  fromList = Tree.fromList

  map : {{Ord b}} -> (a -> b) -> Set a -> Set b
  map = Tree.map

  filter : {{Ord a}} -> (a -> Bool) -> Set a -> Set a
  filter = Tree.filter

  bind : {{Ord b}} -> Set a -> (a -> Set b) -> Set b
  bind m k = unions (Prelude.map k (toList m))

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

  instance
    Foldable-Set : Foldable Set
    Foldable-Set = Tree.Foldable-Tree

    Eq-Set : {{Ord a}} -> Eq (Set a)
    Eq-Set ._==_ xs ys = all (flip member ys) xs && all (flip member xs) ys

    Semigroup-Set : {{Ord a}} -> Semigroup (Set a)
    Semigroup-Set ._<>_ = union

    Monoid-Set : {{Ord a}} -> Monoid (Set a)
    Monoid-Set .mempty = empty

    Show-Set : {{Show a}} -> Show (Set a)
    Show-Set .show = showDefault {{Show-Set}}
    Show-Set .showsPrec prec xs = showsUnaryWith showsPrec "fromList" prec (toList xs)