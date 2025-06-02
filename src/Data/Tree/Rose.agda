module Data.Tree.Rose where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Data.Monoid.Foldable
open import Data.Functor.Compose
open import Data.Functor.Recursive
open import Data.List as List using ()
open import Data.String as String using ()

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a : Type

-------------------------------------------------------------------------------
-- Tree
-------------------------------------------------------------------------------

data Tree (a : Type) : Type where
  node : a -> List (Tree a) -> Tree a

instance
  HasBase-Tree : HasBase (Tree a)
  HasBase-Tree {a} = record { Base = Compose (Tuple a) List }

  Recursive-Tree : Recursive (Tree a)
  Recursive-Tree .project (node x ts) = asCompose (x , ts)

  Functor-Tree : Functor Tree
  Functor-Tree .map f (node x ts) = node (f x) (map (map f) ts)

  Foldable-Tree : Foldable Tree
  Foldable-Tree .foldMap f (node x ts) = f x <> foldMap (foldMap f) ts

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
