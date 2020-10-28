{-# OPTIONS --type-in-type #-}

module Data.Subset where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude hiding (map)

open import Data.Foldable
open import Data.BST.Naive as Tree using (Tree)
open import Data.Traversable

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b : Set

-------------------------------------------------------------------------------
-- Subset
-------------------------------------------------------------------------------

abstract
  Subset : Set -> Set
  Subset a = Tree a

-------------------------------------------------------------------------------
-- Basic operations
-------------------------------------------------------------------------------

  empty : Subset a
  empty = Tree.empty

  singleton : a -> Subset a
  singleton = Tree.singleton

  elems : Subset a -> List a
  elems = toList

  insert : {{_ : Ord a}} -> a -> Subset a -> Subset a
  insert = Tree.insert

  delete : {{_ : Ord a}} -> a -> Subset a -> Subset a
  delete = Tree.delete

  member : {{_ : Ord a}} -> a -> Subset a -> Bool
  member = Tree.member

  union : {{_ : Ord a}} -> Subset a -> Subset a -> Subset a
  union = Tree.merge

  difference : {{_ : Ord a}} -> Subset a -> Subset a -> Subset a
  difference xs ys = foldr Tree.delete xs ys

  intersection : {{_ : Ord a}} -> Subset a -> Subset a -> Subset a
  intersection xs ys = difference xs (difference xs ys)

  fromList : {{_ : Ord a}} -> List a -> Subset a
  fromList = Tree.fromList

  map : {{_ : Ord b}} -> (a -> b) -> Subset a -> Subset b
  map = Tree.map

  filter : {{_ : Ord a}} -> (a -> Bool) -> Subset a -> Subset a
  filter = Tree.filter

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

  instance
    Foldable-Subset : Foldable Subset
    Foldable-Subset .foldMap = foldMap {{Tree.Foldable-Tree}}

    Eq-Subset : {{_ : Ord a}} -> Eq (Subset a)
    Eq-Subset ._==_ xs ys = all (flip member ys) xs && all (flip member xs) ys

    Semigroup-Subset : {{_ : Ord a}} -> Semigroup (Subset a)
    Semigroup-Subset ._<>_ = union

    Monoid-Subset : {{_ : Ord a}} -> Monoid (Subset a)
    Monoid-Subset .mempty = empty

    Show-Subset : {{_ : Show a}} -> Show (Subset a)
    Show-Subset .showsPrec d xs = showParen (d > appPrec)
      (showString "fromList" <<< shows (toList xs))
