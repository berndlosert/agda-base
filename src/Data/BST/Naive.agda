{-# OPTIONS --type-in-type #-}

module Data.BST.Naive where

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
-- Tree
-------------------------------------------------------------------------------

data Tree (a : Set) : Set where
  Leaf : Tree a
  Node : Tree a -> a -> Tree a -> Tree a

-------------------------------------------------------------------------------
-- Basic operations
-------------------------------------------------------------------------------

insert : {{_ : Ord a}} -> a -> Tree a -> Tree a
insert x Leaf = Node Leaf x Leaf
insert x (Node l y r) with compare x y
... | EQ = Node l x r
... | LT = Node (insert x l) y r
... | GT = Node l y (insert x r)

private splitMax : Tree a -> a -> Tree a -> Tree a * a
splitMax t x Leaf = (t , x)
splitMax t x (Node l y r) = let (r' , z) = splitMax l y r in (Node t x r' , z)

merge : Tree a -> Tree a -> Tree a
merge Leaf t = t
merge (Node l x r) t = let (l' , y) = splitMax l x r in Node l' y t

delete : {{_ : Ord a}} -> a -> Tree a -> Tree a
delete _ Leaf = Leaf
delete x (Node l y r) with compare x y
... | EQ = merge l r
... | LT = Node (delete x l) y r
... | GT = Node l y (delete x r)

member : {{_ : Ord a}} -> a -> Tree a -> Bool
member x Leaf = False
member x (Node l y r) with compare x y
... | EQ = True
... | LT = member x l
... | GT = member x r
