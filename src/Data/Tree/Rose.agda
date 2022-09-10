module Data.Tree.Rose where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Data.Foldable
open import Data.Functor.Recursive
open import Data.List as List using ()
open import Data.String as String using ()

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a : Set

-------------------------------------------------------------------------------
-- Tree
-------------------------------------------------------------------------------

data TreeF (a r : Set) : Set where
  node : a -> List r -> TreeF a r

data Tree (a : Set) : Set where
  node : a -> List (Tree a) -> Tree a

instance
  Functor-TreeF : Functor (TreeF a)
  Functor-TreeF .map f (node x rs) = node x (map f rs)

  HasBase-Tree : HasBase (Tree a)
  HasBase-Tree {a} = record { Base = TreeF a }

  Recursive-Tree : Recursive (Tree a)
  Recursive-Tree .project (node x ts) = node x ts

  Functor-Tree : Functor Tree
  Functor-Tree .map f (node x ts) = node (f x) ((map f) <$> ts)

  Foldable-Tree : Foldable Tree
  Foldable-Tree .foldr {a} {b} f z (node x ts) =
      f x (foldr go z ts)
    where
      go : Tree a -> b -> b
      go t z' = foldr f z' t

-------------------------------------------------------------------------------
-- Functions
-------------------------------------------------------------------------------

private
  draw : Tree String -> List String
  draw (node x ts0) = String.lines x <> drawSubTrees ts0
    where
      shift : String -> String -> List String -> List String
      shift first other ss =
        List.zipWith _<>_ (first :: List.replicate (List.length ss) other) ss

      drawSubTrees : List (Tree String) -> List String
      drawSubTrees [] = []
      drawSubTrees (t :: []) =
        "|" :: shift "`- " "   " (draw t)
      drawSubTrees (t :: ts) =
        "|" :: shift "+- " "|  " (draw t) <> drawSubTrees ts

drawTree : Tree String -> String
drawTree = String.unlines <<< draw
