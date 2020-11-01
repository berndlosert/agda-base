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
  data KVPair (k v : Set) : Set where
    KVPair: : k -> v -> KVPair k v

  data Map' (k v : Set) : Set where
    Map: : Tree (KVPair k v) -> Map' k v

Map = Map'

instance
  Eq-KVPair : {{_ : Eq k}} -> Eq (KVPair k v)
  Eq-KVPair ._==_ (KVPair: k _) (KVPair: k' _) = k == k'

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
keys (Map: t) = foldMap (\ { (KVPair: k v) -> [ k ] }) t

elems : Map k v -> List v
elems (Map: t) = foldMap (\ { (KVPair: k v) -> [ v ] }) t

-------------------------------------------------------------------------------
-- Insertion
-------------------------------------------------------------------------------

insert : k -> v -> Map k v -> Map k v
insert k v (Map: t) = {!!}
