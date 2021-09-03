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
    constructor KeyVal:
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
    Dict: : Tree (KeyVal k v) -> Dict' k v

Dict = Dict'

-------------------------------------------------------------------------------
-- Construction
-------------------------------------------------------------------------------

empty : Dict k v
empty = Dict: Tree.empty

singleton : k -> v -> Dict k v
singleton k v = Dict: $ Tree.singleton $ (KeyVal: k v)

-------------------------------------------------------------------------------
-- Destruction
-------------------------------------------------------------------------------

keys : Dict k v -> List k
keys (Dict: t) = foldMap (getKey >>> List.singleton) t

values : Dict k v -> List v
values (Dict: t) = foldMap (getVal >>> List.singleton) t

-------------------------------------------------------------------------------
-- Other operations
-------------------------------------------------------------------------------

insert : {{Ord k}} -> k -> v -> Dict k v -> Dict k v
insert k v (Dict: t) = Dict: (Tree.insert (KeyVal: k v) t)

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
delete k (Dict: t) =
  case Tree.query (compare k <<< getKey) t of \ where
     Nothing -> Dict: t
     (Just p) -> Dict: (Tree.delete p t)

lookup : {{Ord k}} -> k -> Dict k v -> Maybe v
lookup k (Dict: t) =
  maybe Nothing (Just <<< getVal) $ Tree.query (compare k <<< getKey) t

member : {{Ord k}} -> k -> Dict k v -> Bool
member k = maybe False (const True) <<< lookup k

map : {{Ord k}} -> (a -> b) -> Dict k a -> Dict k b
map {a = a} {b = b} f (Dict: t) = Dict: (Tree.map go t)
  where
    go : KeyVal k a -> KeyVal k b
    go (KeyVal: k v) = KeyVal: k (f v)

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

instance
  Foldable-Dict : Foldable (Dict k)
  Foldable-Dict .foldr f z (Dict: t) =
    foldr (\ where (KeyVal: _ x) y -> f x y) z t

  Show-Dict : {{Show k}} -> {{Show v}} -> Show (Dict k v)
  Show-Dict .showsPrec d m = showParen (d > 10) $
    showString "fromList " <<< shows (toList m)
