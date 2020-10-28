{-# OPTIONS --type-in-type #-}

module Data.Subset where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Data.Foldable
open import Data.BST.Naive as Tree using (Tree; Leaf; Node)
open import Data.Traversable

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a : Set

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
  empty = Leaf

  singleton : a -> Subset a
  singleton a = Node Leaf a Leaf

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

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

  instance
    Functor-Subset : Functor Subset
    Functor-Subset .map = map {{Tree.Functor-Tree}}

    Foldable-Subset : Foldable Subset
    Foldable-Subset .foldMap = foldMap {{Tree.Foldable-Tree}}

    Traversable-Subset : Traversable Subset
    Traversable-Subset .traverse = traverse {{Tree.Traversable-Tree}}

    Eq-Subset : {{_ : Ord a}} -> Eq (Subset a)
    Eq-Subset ._==_ xs ys = all (flip member ys) xs && all (flip member xs) ys
