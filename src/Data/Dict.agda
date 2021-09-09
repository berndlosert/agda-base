{-# OPTIONS --type-in-type #-}

module Data.Dict where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude hiding (map)

open import Data.Foldable hiding (toList)
open import Data.List as List using ()
open import Data.Tree.Balanced.TwoThree as Tree using (Tree)
open import String.Show

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b k v : Set

-------------------------------------------------------------------------------
-- KeyVal a b
-------------------------------------------------------------------------------

private
  record KeyVal (a b : Set) : Set where
    constructor toKeyVal
    field
      getKey : a
      getVal : b

open KeyVal

instance
  Eq-KeyVal : {{Eq a}} -> Eq (KeyVal a b)
  Eq-KeyVal ._==_ = equating getKey

  Ord-KeyVal : {{Ord a}} -> Ord (KeyVal a b)
  Ord-KeyVal .compare = comparing getKey

-------------------------------------------------------------------------------
-- Dict
-------------------------------------------------------------------------------

private
  data Dict' (k v : Set) : Set where
    toDict : Tree (KeyVal k v) -> Dict' k v

Dict = Dict'

-------------------------------------------------------------------------------
-- Construction
-------------------------------------------------------------------------------

empty : Dict k v
empty = toDict Tree.empty

singleton : k -> v -> Dict k v
singleton k v = toDict $ Tree.singleton $ (toKeyVal k v)

-------------------------------------------------------------------------------
-- Destruction
-------------------------------------------------------------------------------

keys : Dict k v -> List k
keys (toDict t) = foldMap (getKey >>> List.singleton) t

values : Dict k v -> List v
values (toDict t) = foldMap (getVal >>> List.singleton) t

-------------------------------------------------------------------------------
-- Other operations
-------------------------------------------------------------------------------

insert : {{Ord k}} -> k -> v -> Dict k v -> Dict k v
insert k v (toDict t) = toDict (Tree.insert (toKeyVal k v) t)

fromList : {{Ord k}} -> List (Pair k v) -> Dict k v
fromList [] = empty
fromList {k} {v} kvs = go kvs empty
  where
    go : List (Pair k v) -> Dict k v -> Dict k v
    go [] d = d
    go ((k , v) :: rest) d = go rest (insert k v d)

toList : Dict k v -> List (Pair k v)
toList d = List.zip (keys d) (values d)

delete : {{Ord k}} -> k -> Dict k v -> Dict k v
delete k (toDict t) =
  case Tree.query (compare k <<< getKey) t of \ where
     nothing -> toDict t
     (just p) -> toDict (Tree.delete p t)

lookup : {{Ord k}} -> k -> Dict k v -> Maybe v
lookup k (toDict t) =
  maybe nothing (just <<< getVal) $ Tree.query (compare k <<< getKey) t

member : {{Ord k}} -> k -> Dict k v -> Bool
member k = maybe false (const true) <<< lookup k

map : {{Ord k}} -> (a -> b) -> Dict k a -> Dict k b
map {a = a} {b = b} f (toDict t) = toDict (Tree.map go t)
  where
    go : KeyVal k a -> KeyVal k b
    go (toKeyVal k v) = toKeyVal k (f v)

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

instance
  Foldable-Dict : Foldable (Dict k)
  Foldable-Dict .foldr f z (toDict t) =
    foldr (\ where (toKeyVal _ x) y -> f x y) z t

  Show-Dict : {{Show k}} -> {{Show v}} -> Show (Dict k v)
  Show-Dict .showsPrec d m = showParen (d > 10) $
    showString "fromList " <<< shows (toList m)
