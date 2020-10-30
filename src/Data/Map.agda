{-# OPTIONS --type-in-type #-}

module Data.Map where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Data.Foldable
open import Data.List as List using ()

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    k v : Set

-------------------------------------------------------------------------------
-- Map
-------------------------------------------------------------------------------

private
  data Map' (k v : Set) : Set where
    Leaf : Map' k v
    Two : Map' k v -> k -> v -> Map' k v -> Map' k v
    Three : Map' k v -> k -> v -> Map' k v -> k -> v -> Map' k v -> Map' k v

Map = Map'

-------------------------------------------------------------------------------
-- Construction
-------------------------------------------------------------------------------

empty : Map k v
empty = Leaf

singleton : k -> v -> Map k v
singleton k v = Two Leaf k v Leaf

-------------------------------------------------------------------------------
-- Destruction
-------------------------------------------------------------------------------

keys : Map k v -> List k
keys Leaf = []
keys (Two l k v r) = keys l <> [ k ] <> keys r
keys (Three l k v m k' v' r) = keys l <> [ k ] <> keys m <> [ k' ] <> keys r

elems : Map k v -> List v
elems Leaf = []
elems (Two l k v r) = elems l <> [ v ] <> elems r
elems (Three l k v m k' v' r) = elems l <> [ v ] <> elems m <> [ v' ] <> elems r

-------------------------------------------------------------------------------
-- Helpers for inserting and deleting
-------------------------------------------------------------------------------

private
  data TreeContext (k v : Set) : Set where
    TwoLeft : k -> v -> Map k v -> TreeContext k v
    TwoRight : Map k v -> k -> v -> TreeContext k v
    ThreeLeft : k -> v -> Map k v -> k -> v -> Map k v -> TreeContext k v
    ThreeMiddle : Map k v -> k -> v -> k -> v -> Map k v -> TreeContext k v
    ThreeRight : Map k v -> k -> v -> Map k v -> k -> v -> TreeContext k v

  data KickUp (k v : Set) : Set where
    KickUp: : Map k v -> k -> v -> Map k v -> KickUp k v

  module _ {{_ : Ord k}} where

    fromZipper : List (TreeContext k v) -> Map k v -> Map k v
    fromZipper [] t = t
    fromZipper (x :: ctx) t with x
    ... | TwoLeft k v r = fromZipper ctx (Two t k v r)
    ... | TwoRight l k v = fromZipper ctx (Two l k v t)
    ... | ThreeLeft k v m k' v' r = fromZipper ctx (Three t k v m k' v' r)
    ... | ThreeMiddle l k v k' v' r = fromZipper ctx (Three l k v t k' v' r)
    ... | ThreeRight l k v m k' v' = fromZipper ctx (Three l k v m k' v' t)

    insertUp : List (TreeContext k v) -> KickUp k v -> Map k v
    insertUp [] (KickUp: l k' v' r) = Two l k' v' r
    insertUp (x :: ctx) kup with x | kup
    ... | TwoLeft k1 v1 r | KickUp: l k' v' m =
      fromZipper ctx (Three l k' v' m k1 v1 r)
    ... | TwoRight l k1 v1 | KickUp: m k' v' r =
      fromZipper ctx (Three l k1 v1 m k' v' r)
    ... | ThreeLeft k1 v1 c k2 v2 d | KickUp: a k' v' b =
      insertUp ctx (KickUp: (Two a k' v' b) k1 v1 (Two c k2 v2 d))
    ... | ThreeMiddle a k1 v1 k2 v2 d | KickUp: b k' v' c =
      insertUp ctx (KickUp: (Two a k1 v1 b) k' v' (Two c k2 v2 d))
    ... | ThreeRight a k1 v1 b k2 v2 | KickUp: c k' v' d =
      insertUp ctx (KickUp: (Two a k1 v1 b) k2 v2 (Two c k' v' d))

    insertDown : k -> v -> List (TreeContext k v) -> Map k v -> Map k v
    insertDown k v ctx Leaf = insertUp ctx (KickUp: Leaf k v Leaf)
    insertDown k v ctx (Two l k1 v1 r) with compare k k1
    ... | EQ = fromZipper ctx (Two l k v r)
    ... | LT = insertDown k v (TwoLeft k1 v1 r :: ctx) l
    ... | GT = insertDown k v (TwoRight l k1 v1 :: ctx) r
    insertDown k v ctx (Three l k1 v1 m k2 v2 r)
      with compare k k1 | compare k k2
    ... | EQ | _ = fromZipper ctx (Three l k v m k2 v2 r)
    ... | _ | EQ = fromZipper ctx (Three l k1 v1 m k v r)
    ... | LT | _ = insertDown k v (ThreeLeft k1 v1 m k2 v2 r :: ctx) l
    ... | GT | LT = insertDown k v (ThreeMiddle l k1 v1 k2 v2 r :: ctx) m
    ... | _ | _ = insertDown k v (ThreeRight l k1 v1 m k2 v2 :: ctx) r

-------------------------------------------------------------------------------
-- Inserting
-------------------------------------------------------------------------------

--insert : {{_ : Ord k}} -> k -> v -> Map k v -> Map k v
--insert k v = down []
--  where

-------------------------------------------------------------------------------
-- Deleting
-------------------------------------------------------------------------------

--delete : {{_ : Eq k}} -> k -> Map k v -> Map k v
--delete _ [] = []
--delete k (h :: t) = if fst h == k then t else delete k t

-------------------------------------------------------------------------------
-- Updating
-------------------------------------------------------------------------------

--adjust : {{_ : Eq k}} -> (v -> v) -> k -> Map k v -> Map k v
--adjust _ _ [] = []
--adjust f k (h :: t) =
--  if fst h == k
--  then (k , f (snd h)) :: t
--  else adjust f k t

-------------------------------------------------------------------------------
-- Querying
-------------------------------------------------------------------------------

--lookup : {{_ : Eq k}} -> k -> Map k v -> Maybe v
--lookup _ [] = Nothing
--lookup k (h :: t) = if fst h == k then Just (snd h) else lookup k t

--member : {{_ : Eq k}} -> k -> Map k v -> Bool
--member _ [] = False
--member k (h :: t) = if fst h == k then True else member k t

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

--instance
--  Functor-Map : Functor (Map k)
--  Functor-Map .map f = map \ {(k , v) -> (k , f v)}
--
--  Foldable-Map : Foldable (Map k)
--  Foldable-Map .foldMap f = List.foldMap \ {(k , v) ->  f v}
