{-# OPTIONS --type-in-type #-}

module Data.Dict where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude hiding (map)

open import Data.Foldable hiding (toList)
open import Data.List as List using ()
open import Data.Tree.Balanced.TwoThree as Tree using (Tree)

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b k v : Type

-------------------------------------------------------------------------------
-- KVPair
-------------------------------------------------------------------------------

private
  record KVPair (k v : Type) : Type where
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
  data Dict' (k v : Type) : Type where
    Dict: : Tree (KVPair k v) -> Dict' k v

Dict = Dict'

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
keys (Dict: t) = foldMap (getKey >>> List.singleton) t

values : Dict k v -> List v
values (Dict: t) = foldMap (getValue >>> List.singleton) t

-------------------------------------------------------------------------------
-- Other operations
-------------------------------------------------------------------------------

insert : {{_ : Ord k}} -> k -> v -> Dict k v -> Dict k v
insert k v (Dict: t) = Dict: (Tree.insert (KVPair: k v) t)

fromList : {{_ : Ord k}} -> List (k * v) -> Dict k v
fromList [] = empty
fromList {k} {v} kvs = go kvs empty
  where
    go : List (k * v) -> Dict k v -> Dict k v
    go [] d = d
    go ((k , v) :: rest) d = go rest (insert k v d)

toList : Dict k v -> List (k * v)
toList d = List.zip (keys d) (values d)

delete : {{_ : Ord k}} -> k -> Dict k v -> Dict k v
delete k (Dict: t) =
  case find (\ p -> k == getKey p) t of \ where
     Nothing -> Dict: t
     (Just p) -> Dict: (Tree.delete p t)

-- N.B. uses undefined, but that's OK since we never look at the
-- values.
member : {{_ : Ord k}} -> k -> Dict k v -> Bool
member k (Dict: t) = Tree.member (KVPair: k undefined) t

lookup : {{_ : Ord k}}
  -> (key : k)
  -> (dict : Dict k v)
  -> {{_ : Assert $ member key dict}}
  -> v
lookup k (Dict: t) = fromJust res {{trustMe}}
  where
    t' = flip Tree.mapMonotonic t \ where (KVPair: k v) -> (k , v)
    res = Tree.lookup k t'

map : {{_ : Ord k}} -> (a -> b) -> Dict k a -> Dict k b
map f (Dict: t) = Dict: $ flip Tree.map t \ where
  (KVPair: k v) -> KVPair: k (f v)

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

instance
  Foldable-Dict : Foldable (Dict k)
  Foldable-Dict .foldr f z (Dict: t) =
    foldr (\ where (KVPair: k v) y -> f v y) z t

  Show-Dict : {{_ : Show k}} {{_ : Show v}} -> Show (Dict k v)
  Show-Dict .showsPrec d m = showParen (d > 10) $
    showString "fromList " <<< shows (toList m)
