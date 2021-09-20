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

record Dict (k v : Set) : Set where
  constructor toDict
  field unDict : Tree (KeyVal k v)

open Dict

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
keys kvs = foldMap (getKey >>> List.singleton) (unDict kvs)

values : Dict k v -> List v
values kvs = foldMap (getVal >>> List.singleton) (unDict kvs)

-------------------------------------------------------------------------------
-- Other operations
-------------------------------------------------------------------------------

insert : {{Ord k}} -> k -> v -> Dict k v -> Dict k v
insert k v kvs = toDict (Tree.insert (toKeyVal k v) (unDict kvs))

fromList : {{Ord k}} -> List (Pair k v) -> Dict k v
fromList [] = empty
fromList {k} {v} kvs = go kvs empty
  where
    go : List (Pair k v) -> Dict k v -> Dict k v
    go [] d = d
    go ((k , v) :: rest) d = go rest (insert k v d)

toList : Dict k v -> List (Pair k v)
toList kvs = List.zip (keys kvs) (values kvs)

delete : {{Ord k}} -> k -> Dict k v -> Dict k v
delete k kvs =
  let t = unDict kvs
  in case Tree.query (compare k <<< getKey) t of \ where
     nothing -> toDict t
     (just p) -> toDict (Tree.delete p t)

lookup : {{Ord k}} -> k -> Dict k v -> Maybe v
lookup k kvs =
  let res = Tree.query (compare k <<< getKey) (unDict kvs)
  in maybe nothing (just <<< getVal) res

member : {{Ord k}} -> k -> Dict k v -> Bool
member k = maybe false (const true) <<< lookup k

map : {{Ord k}} -> (a -> b) -> Dict k a -> Dict k b
map {a = a} {b = b} f kvs = toDict (Tree.map go (unDict kvs))
  where
    go : KeyVal k a -> KeyVal k b
    go (toKeyVal k v) = toKeyVal k (f v)

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

instance
  Foldable-Dict : Foldable (Dict k)
  Foldable-Dict .foldr f z kvs =
    foldr (\ where (toKeyVal _ x) y -> f x y) z (unDict kvs)

  Show-Dict : {{Show k}} -> {{Show v}} -> Show (Dict k v)
  Show-Dict .showsPrec d kvs = showParen (d > 10) $
    showString "fromList " <<< shows (toList kvs)
