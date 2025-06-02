module Data.Tree.Unbalanced.Binary where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude hiding (map)

open import Data.Monoid.Foldable
open import Data.String.Show
open import Data.Traversable

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b : Type

-------------------------------------------------------------------------------
-- Tree
-------------------------------------------------------------------------------

data Tree (a : Type) : Type where
  leaf : Tree a
  node : Tree a -> a -> Tree a -> Tree a

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

instance
  Foldable-Tree : Foldable Tree
  Foldable-Tree .foldMap f = \ where
    leaf -> mempty
    (node l x r) -> foldMap f l <> f x <> foldMap f r

  Eq-Tree : {{Eq a}} -> Eq (Tree a)
  Eq-Tree ._==_ = \ where
    leaf leaf -> true
    leaf _ -> false
    _ leaf -> false
    (node l x r) (node l1 x1 r1) -> x == x1 && l == l1 && r == r1

  Show-Tree : {{Show a}} -> Show (Tree a)
  Show-Tree .show = showDefault
  Show-Tree .showsPrec prec leaf = "leaf"
  Show-Tree .showsPrec prec (node l x r) = showParen (prec > appPrec)
    "node "
      <> showsPrec appPrec+1 l <> " "
      <> showsPrec appPrec+1 x <> " "
      <> showsPrec appPrec+1 r

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
    case (compare x y) \ where
      equal -> node l x r
      less -> node (insert x l) y r
      greater -> node l y (insert x r)

  merge : Tree a -> Tree a -> Tree a
  merge leaf t = t
  merge t leaf = t
  merge t@(node _ x _) s@(node _ y _) =
    if x <= y
      then foldr insert s t
      else foldr insert t s

  delMin : Tree a -> Maybe (Tuple a (Tree a))
  delMin (node leaf x r) = just (x , r)
  delMin (node l x r) = do
    (y , l1) <- delMin l
    pure (y , node l1 x r)
  delMin _ = nothing

  delete : a -> Tree a -> Tree a
  delete _ leaf = leaf
  delete x (node l y r) =
    case (compare x y , l , r) \ where
      (less , _ , _) -> node (delete x l) y r
      (greater , _ , _) -> node l y (delete x r)
      (equal , leaf ,  _) -> r
      (equal , _ , leaf) -> l
      (equal , _ , t) -> case (delMin t) \ where
        (just (z , r1)) -> node l z r1
        nothing -> l

  member : a -> Tree a -> Bool
  member x leaf = false
  member x (node l y r) =
    case (compare x y) \ where
      equal -> true
      less -> member x l
      greater -> member x r

  fromList : List a -> Tree a
  fromList xs = foldr insert xs leaf

map : {{Ord b}} -> (a -> b) -> Tree a -> Tree b
map f = fromList <<< Prelude.map f <<< toList

filter : {{Ord a}} -> (a -> Bool) -> Tree a -> Tree a
filter _ leaf = leaf
filter p (node l x r) =
  let
    l1 = filter p l
    r1 = filter p r
  in
    if p x then node l1 x r1 else merge l1 r1
