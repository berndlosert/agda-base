{-# OPTIONS --type-in-type #-}

module Data.Map where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Data.Foldable
open import Data.Tree.Balanced.TwoThree as Tree using (Tree)

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    k v : Set

-------------------------------------------------------------------------------
-- KVPair & Map
-------------------------------------------------------------------------------

private
  record KVPair (k v : Set) : Set where
    constructor KVPair:
    field
      getKey : k
      getValue : v

  open KVPair

  data Map' (k v : Set) : Set where
    Map: : Tree (KVPair k v) -> Map' k v

Map = Map'

instance
  Eq-KVPair : {{_ : Eq k}} -> Eq (KVPair k v)
  Eq-KVPair ._==_ x y = getKey x == getKey y

  Ord-KVPair : {{_ : Ord k}} -> Ord (KVPair k v)
  Ord-KVPair ._<_ x y = getKey x < getKey y

-------------------------------------------------------------------------------
-- Construction
-------------------------------------------------------------------------------

empty : Map k v
empty = Map: Tree.empty

singleton : k -> v -> Map k v
singleton k v = Map: $ Tree.singleton $ KVPair: k v

-------------------------------------------------------------------------------
-- Destruction
-------------------------------------------------------------------------------

keys : Map k v -> List k
keys (Map: t) = foldMap (getKey >>> [_]) t

values : Map k v -> List v
values (Map: t) = foldMap (getValue >>> [_]) t

-------------------------------------------------------------------------------
-- Insertion & Deletion
-------------------------------------------------------------------------------

insert : {{_ : Ord k}} -> k -> v -> Map k v -> Map k v
insert k v (Map: t) = Map: (Tree.insert (KVPair: k v) t)

delete : {{_ : Ord k}} -> k -> Map k v -> Map k v
delete k (Map: t) with find (\ p -> k == getKey p) t
... | Nothing = Map: t
... | Just p = Map: (Tree.delete p t)
