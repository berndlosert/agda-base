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
  leaf : Tree a
  node : Tree a -> a -> Tree a -> Tree a

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

instance
  Foldable-Tree : Foldable Tree
  Foldable-Tree .foldr f z = \ where
    leaf -> z
    (node l x r) -> foldr f (f x (foldr f z r)) l

  Eq-Tree : {{Eq a}} -> Eq (Tree a)
  Eq-Tree ._==_ = \ where
    leaf leaf -> true
    leaf _ -> false
    _ leaf -> false
    (node l x r) (node l' x' r') -> x == x' && l == l' && r == r'

  Show-Tree : {{Show a}} -> Show (Tree a)
  Show-Tree .showsPrec _ leaf = showString "leaf"
  Show-Tree .showsPrec d (node l x r) = showParen (d > appPrec)
    (showString "node "
    <<< showsPrec appPrec+1 l
    <<< showString " "
    <<< showsPrec appPrec+1 x
    <<< showString " "
    <<< showsPrec appPrec+1 r)

-------------------------------------------------------------------------------
-- Basic operations
-------------------------------------------------------------------------------

empty : Tree a
empty = leaf

singleton : a -> Tree a
singleton x = node leaf x leaf

module _ {{_ : Ord a}} where

  insert : a -> Tree a -> Tree a
  insert x leaf = node leaf x leaf
  insert x (node l y r) =
    case compare x y of \ where
      EQ -> node l x r
      LT -> node (insert x l) y r
      GT -> node l y (insert x r)

  merge : Tree a -> Tree a -> Tree a
  merge leaf t = t
  merge t leaf = t
  merge t@(node _ x _) s@(node _ y _) =
    if x <= y
      then foldr insert s t
      else foldr insert t s

  delMin : (t : Tree a) -> {{Assumes $ not (null t)}} -> Pair a (Tree a)
  delMin (node leaf x r) = (x , r)
  delMin (node l@(node _ _ _) x r) =
    let (y , l') = delMin l
    in (y , node l' x r)
  delMin _ = error "Data.Tree.Unbalanced.delMin: bad argument"

  delete : a -> Tree a -> Tree a
  delete _ leaf = leaf
  delete x (node l y r) = unsafePerform $
    case (compare x y , l , r) of \ where
      (LT , _ , _) -> node (delete x l) y r
      (GT , _ , _) -> node l y (delete x r)
      (EQ , leaf ,  _) -> r
      (EQ , _ , leaf) -> l
      (EQ , _ , t) -> let (z , r') = delMin t in node l z r'

  member : a -> Tree a -> Bool
  member x leaf = false
  member x (node l y r) =
    case compare x y of \ where
      EQ -> true
      LT -> member x l
      GT -> member x r

  fromList : List a -> Tree a
  fromList = foldr insert leaf

map : {{Ord b}} -> (a -> b) -> Tree a -> Tree b
map f = fromList <<< Prelude.map f <<< toList

filter : {{Ord a}} -> (a -> Bool) -> Tree a -> Tree a
filter _ leaf = leaf
filter p (node l x r) =
  let
    l' = filter p l
    r' = filter p r
  in
    if p x then node l' x r' else merge l' r'
