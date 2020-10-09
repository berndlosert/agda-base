{-# OPTIONS --type-in-type #-}

module Data.Map where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Data.Foldable

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    k v : Set

-------------------------------------------------------------------------------
-- Map
-------------------------------------------------------------------------------

-- This is a list-backed implememntation because:
--  * it's easy
--  * the AVL tree implemenation in agda-stdlib is complicated and requires
--    too much proof infrastructure
--  * Idris's SortedMap makes no sense to me
--  * Haskell tree-based implemenations require too many partial functions

abstract
  Map : (k v : Set) -> Set
  Map k v = List (k * v)

-------------------------------------------------------------------------------
-- Construction
-------------------------------------------------------------------------------

  nil : Map k v
  nil = []

  singleton : k -> v -> Map k v
  singleton k v = [(k , v)]

-------------------------------------------------------------------------------
-- Destruction
-------------------------------------------------------------------------------

  keys : Map k v -> List k
  keys = map fst

  elems : Map k v -> List v
  elems = map snd

-------------------------------------------------------------------------------
-- Inserting
-------------------------------------------------------------------------------

  insert : {{_ : Eq k}} -> k -> v -> Map k v -> Map k v
  insert k v [] = singleton k v
  insert k v (h :: t) =
    if fst h == k
      then (k , v) :: t
      else h :: insert k v t

-------------------------------------------------------------------------------
-- Deleting
-------------------------------------------------------------------------------

  delete : {{_ : Eq k}} -> k -> Map k v -> Map k v
  delete _ [] = []
  delete k (h :: t) = if fst h == k then t else delete k t

-------------------------------------------------------------------------------
-- Updating
-------------------------------------------------------------------------------

  adjust : {{_ : Eq k}} -> (v -> v) -> k -> Map k v -> Map k v
  adjust _ _ [] = []
  adjust f k (h :: t) =
    if fst h == k
    then (k , f (snd h)) :: t
    else adjust f k t

-------------------------------------------------------------------------------
-- Querying
-------------------------------------------------------------------------------

  lookup : {{_ : Eq k}} -> k -> Map k v -> Maybe v
  lookup _ [] = Nothing
  lookup k (h :: t) = if fst h == k then Just (snd h) else lookup k t

  member : {{_ : Eq k}} -> k -> Map k v -> Bool
  member _ [] = False
  member k (h :: t) = if fst h == k then True else member k t

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

  instance
    Functor-Map : Functor (Map k)
    Functor-Map .map f = map \ {(k , v) -> (k , f v)}

    Foldable-Map : Foldable (Map k)
    Foldable-Map .foldMap f = foldMap \ {(k , v) ->  f v}
