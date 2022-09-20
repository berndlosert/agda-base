module Data.Map where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude hiding (map)

open import Data.Foldable hiding (toList)
open import Data.List as List using ()
open import Data.String.Builder hiding (singleton)
open import Data.String.Show
open import Data.Tree.Balanced.TwoThree as Tree using (Tree)

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
    constructor asKeyVal
    field
      getKey : a
      getVal : b

open KeyVal

instance
  Eq-KeyVal : {{Eq a}} -> Eq (KeyVal a b)
  Eq-KeyVal ._==_ = _==_ on getKey

  Ord-KeyVal : {{Ord a}} -> Ord (KeyVal a b)
  Ord-KeyVal ._<_ = _<_ on getKey

-------------------------------------------------------------------------------
-- Map
-------------------------------------------------------------------------------

record Map (k v : Set) : Set where
  constructor asMap
  field unMap : Tree (KeyVal k v)

open Map

-------------------------------------------------------------------------------
-- Construction
-------------------------------------------------------------------------------

empty : Map k v
empty = asMap Tree.empty

singleton : k -> v -> Map k v
singleton k v = asMap $ Tree.singleton $ (asKeyVal k v)

-------------------------------------------------------------------------------
-- Destruction
-------------------------------------------------------------------------------

keys : Map k v -> List k
keys kvs = foldMap (getKey >>> List.singleton) (unMap kvs)

values : Map k v -> List v
values kvs = foldMap (getVal >>> List.singleton) (unMap kvs)

-------------------------------------------------------------------------------
-- Other operations
-------------------------------------------------------------------------------

insert : {{Ord k}} -> k -> v -> Map k v -> Map k v
insert k v kvs = asMap (Tree.insert (asKeyVal k v) (unMap kvs))

fromList : {{Ord k}} -> List (Pair k v) -> Map k v
fromList [] = empty
fromList {k} {v} kvs = go kvs empty
  where
    go : List (Pair k v) -> Map k v -> Map k v
    go [] d = d
    go ((k , v) :: rest) d = go rest (insert k v d)

toList : Map k v -> List (Pair k v)
toList kvs = List.zip (keys kvs) (values kvs)

delete : {{Ord k}} -> k -> Map k v -> Map k v
delete k kvs =
  let t = unMap kvs
  in case Tree.query (compare k <<< getKey) t of \ where
     nothing -> asMap t
     (just p) -> asMap (Tree.delete p t)

lookup : {{Ord k}} -> k -> Map k v -> Maybe v
lookup k kvs =
  let res = Tree.query (compare k <<< getKey) (unMap kvs)
  in maybe nothing (just <<< getVal) res

member : {{Ord k}} -> k -> Map k v -> Bool
member k = maybe false (const true) <<< lookup k

map : {{Ord k}} -> (a -> b) -> Map k a -> Map k b
map {a = a} {b = b} f kvs = asMap (Tree.map go (unMap kvs))
  where
    go : KeyVal k a -> KeyVal k b
    go (asKeyVal k v) = asKeyVal k (f v)

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

instance
  Foldable-Map : Foldable (Map k)
  Foldable-Map .foldr step init kvs =
    foldr (\ where (asKeyVal _ x) acc -> step x acc) init (unMap kvs)

  Show-Map : {{Show k}} -> {{Show v}} -> Show (Map k v)
  Show-Map .show = showDefault
  Show-Map .showsPrec prec kvs = showParen (prec > 10)
    ("fromList " <> showsPrec prec (toList kvs))
