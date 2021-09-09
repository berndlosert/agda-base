{-# OPTIONS --type-in-type #-}

module Data.Tree.Unbalanced.Binary where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude hiding (map)

open import Data.Foldable
open import Data.Traversable
open import String.Show

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b : Set

-------------------------------------------------------------------------------
-- Tree
-------------------------------------------------------------------------------

data Tree (a : Set) : Set where
  Leaf : Tree a
  Node : Tree a -> a -> Tree a -> Tree a

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

instance
  Foldable-Tree : Foldable Tree
  Foldable-Tree .foldr f z = \ where
    Leaf -> z
    (Node l x r) -> foldr f (f x (foldr f z r)) l

  Eq-Tree : {{Eq a}} -> Eq (Tree a)
  Eq-Tree ._==_ = \ where
    Leaf Leaf -> true
    Leaf _ -> false
    _ Leaf -> false
    (Node l x r) (Node l' x' r') -> x == x' && l == l' && r == r'

  Show-Tree : {{Show a}} -> Show (Tree a)
  Show-Tree .showsPrec _ Leaf = showString "Leaf"
  Show-Tree .showsPrec d (Node l x r) = showParen (d > appPrec)
    (showString "Node "
    <<< showsPrec appPrec+1 l
    <<< showString " "
    <<< showsPrec appPrec+1 x
    <<< showString " "
    <<< showsPrec appPrec+1 r)

-------------------------------------------------------------------------------
-- Basic operations
-------------------------------------------------------------------------------

empty : Tree a
empty = Leaf

singleton : a -> Tree a
singleton x = Node Leaf x Leaf

module _ {{_ : Ord a}} where

  insert : a -> Tree a -> Tree a
  insert x Leaf = Node Leaf x Leaf
  insert x (Node l y r) =
    case compare x y of \ where
      EQ -> Node l x r
      LT -> Node (insert x l) y r
      GT -> Node l y (insert x r)

  merge : Tree a -> Tree a -> Tree a
  merge Leaf t = t
  merge t Leaf = t
  merge t@(Node _ x _) s@(Node _ y _) =
    if x <= y
      then foldr insert s t
      else foldr insert t s

  delMin : {{Partial}} -> Tree a -> Pair a (Tree a)
  delMin (Node Leaf x r) = (x , r)
  delMin (Node l@(Node _ _ _) x r) =
    let (y , l') = delMin l
    in (y , Node l' x r)
  delMin _ = undefined

  delete : a -> Tree a -> Tree a
  delete _ Leaf = Leaf
  delete x (Node l y r) = unsafePerform $
    case (compare x y , l , r) of \ where
      (LT , _ , _) -> Node (delete x l) y r
      (GT , _ , _) -> Node l y (delete x r)
      (EQ , Leaf ,  _) -> r
      (EQ , _ , Leaf) -> l
      (EQ , _ , t) -> let (z , r') = delMin t in Node l z r'

  member : a -> Tree a -> Bool
  member x Leaf = false
  member x (Node l y r) =
    case compare x y of \ where
      EQ -> true
      LT -> member x l
      GT -> member x r

  fromList : List a -> Tree a
  fromList = foldr insert Leaf

map : {{Ord b}} -> (a -> b) -> Tree a -> Tree b
map f = fromList <<< Prelude.map f <<< toList

filter : {{Ord a}} -> (a -> Bool) -> Tree a -> Tree a
filter _ Leaf = Leaf
filter p (Node l x r) =
  let
    l' = filter p l
    r' = filter p r
  in
    if p x then Node l' x r' else merge l' r'
