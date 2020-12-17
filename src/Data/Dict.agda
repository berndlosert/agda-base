{-# OPTIONS --type-in-type #-}

module Data.Dict where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude hiding (map)

open import Data.Foldable
open import Data.Tree.Balanced.TwoThree as Tree using (Tree)

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b k v : Set

-------------------------------------------------------------------------------
-- KVPair
-------------------------------------------------------------------------------

private
  record KVPair (k v : Set) : Set where
    constructor KVPair:
    field
      getKey : k
      getValue : v

  open KVPair

instance
  Eq-KVPair : {{_ : Eq k}} -> Eq (KVPair k v)
  Eq-KVPair ._==_ x y = getKey x == getKey y

  Ord-KVPair : {{_ : Ord k}} -> Ord (KVPair k v)
  Ord-KVPair ._<_ x y = getKey x < getKey y


-------------------------------------------------------------------------------
-- Dict
-------------------------------------------------------------------------------

private
  data Dict' (k v : Set) : Set where
    Dict: : Tree (KVPair k v) -> Dict' k v

Dict = Dict'

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

instance
  Foldable-Dict : Foldable (Dict k)
  Foldable-Dict .foldMap f (Dict: t) = flip foldMap t \ where
    (KVPair: k v) -> f v

-------------------------------------------------------------------------------
-- Construction
-------------------------------------------------------------------------------

empty : Dict k v
empty = Dict: Tree.empty

singleton : k -> v -> Dict k v
singleton k v = Dict: $ Tree.singleton $ KVPair: k v

-------------------------------------------------------------------------------
-- Destruction
-------------------------------------------------------------------------------

keys : Dict k v -> List k
keys (Dict: t) = foldMap (getKey >>> [_]) t

values : Dict k v -> List v
values (Dict: t) = foldMap (getValue >>> [_]) t

-------------------------------------------------------------------------------
-- Other operations
-------------------------------------------------------------------------------

insert : {{_ : Ord k}} -> k -> v -> Dict k v -> Dict k v
insert k v (Dict: t) = Dict: (Tree.insert (KVPair: k v) t)

delete : {{_ : Ord k}} -> k -> Dict k v -> Dict k v
delete k (Dict: t) with find (\ p -> k == getKey p) t
... | Nothing = Dict: t
... | Just p = Dict: (Tree.delete p t)

lookup : {{_ : Ord k}} -> k -> Dict k v -> Maybe v
lookup k (Dict: t) = Tree.lookup k (flip Tree.mapMonotonic t \ where
  (KVPair: k v) -> (k , v))

map : {{_ : Ord k}} -> (a -> b) -> Dict k a -> Dict k b
map f (Dict: t) = Dict: $ flip Tree.map t \ where
  (KVPair: k v) -> KVPair: k (f v)
