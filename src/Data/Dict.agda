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
  Eq-KVPair : {{Eq k}} -> Eq (KVPair k v)
  Eq-KVPair ._==_ x y = getKey x == getKey y

  Ord-KVPair : {{Ord k}} -> Ord (KVPair k v)
  Ord-KVPair .compare x y = compare (getKey x) (getKey y)

-------------------------------------------------------------------------------
-- Dict
-------------------------------------------------------------------------------

private
  data Dict' (k v : Set) : Set where
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
-- Key membership
-------------------------------------------------------------------------------

-- N.B. uses undefined, but that's OK since we never look at the
-- values.
member : {{Ord k}} -> k -> Dict k v -> Bool
member k (Dict: t) = Tree.member (KVPair: k undefined) t

data Key {{_ : Ord k}} (dict : Dict k v) : Set where
  Key: : (key : k) -> {{Assert $ member key dict}} -> Key dict

member' : {{_ : Ord k}} -> k -> (dict : Dict k v) -> Maybe (Key dict)
member' key dict =
  if member key dict
    then Just (Key: key {{trustMe}})
    else Nothing

-------------------------------------------------------------------------------
-- Other operations
-------------------------------------------------------------------------------

insert : {{Ord k}} -> k -> v -> Dict k v -> Dict k v
insert k v (Dict: t) = Dict: (Tree.insert (KVPair: k v) t)

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
  case find (\ p -> k == getKey p) t of \ where
     Nothing -> Dict: t
     (Just p) -> Dict: (Tree.delete p t)

lookup : {{_ : Ord k}} (dict : Dict k v) -> Key dict -> v
lookup (Dict: t) (Key: k) = fromJust res {{trustMe}}
  where
    t' = flip Tree.mapMonotonic t \ where (KVPair: k v) -> (k , v)
    res = Tree.lookup k t'

map : {{Ord k}} -> (a -> b) -> Dict k a -> Dict k b
map f (Dict: t) = Dict: $ flip Tree.map t \ where
  (KVPair: k v) -> KVPair: k (f v)

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

instance
  Foldable-Dict : Foldable (Dict k)
  Foldable-Dict .foldr f z (Dict: t) =
    foldr (\ where (KVPair: k v) y -> f v y) z t

  Show-Dict : {{Show k}} -> {{Show v}} -> Show (Dict k v)
  Show-Dict .showsPrec d m = showParen (d > 10) $
    showString "fromList " <<< shows (toList m)
