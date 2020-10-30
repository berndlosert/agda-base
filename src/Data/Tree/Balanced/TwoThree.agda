{-# OPTIONS --type-in-type #-}

module Data.Tree.Balanced.TwoThree where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Data.Foldable

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b : Set

-------------------------------------------------------------------------------
-- Tree
-------------------------------------------------------------------------------

data Tree (a : Set) : Set where
  Leaf : Tree a
  Two : Tree a -> a -> Tree a -> Tree a
  Three : Tree a -> a -> Tree a -> a -> Tree a -> Tree a

-------------------------------------------------------------------------------
-- Construction
-------------------------------------------------------------------------------

empty : Tree a
empty = Leaf

singleton : a -> Tree a
singleton x = Two Leaf x Leaf

-------------------------------------------------------------------------------
-- Destruction
-------------------------------------------------------------------------------


-------------------------------------------------------------------------------
-- Helpers for inserting and deleting
-------------------------------------------------------------------------------

private
  data TreeContext (a : Set) : Set where
    TwoLeft : a -> Tree a -> TreeContext a
    TwoRight : Tree a -> a -> TreeContext a
    ThreeLeft : a -> Tree a -> a -> Tree a -> TreeContext a
    ThreeMiddle : Tree a -> a -> a -> Tree a -> TreeContext a
    ThreeRight : Tree a -> a -> Tree a -> a -> TreeContext a

  data KickUp (a : Set) : Set where
    KickUp: : Tree a -> a -> Tree a -> KickUp a

  module _ {{_ : Ord a}} where

    fromZipper : List (TreeContext a) -> Tree a -> Tree a
    fromZipper [] t = t
    fromZipper (h :: ctx) t with h
    ... | TwoLeft x r = fromZipper ctx (Two t x r)
    ... | TwoRight l x = fromZipper ctx (Two l x t)
    ... | ThreeLeft x m y r = fromZipper ctx (Three t x m y r)
    ... | ThreeMiddle l x y r = fromZipper ctx (Three l x t y r)
    ... | ThreeRight l x m y = fromZipper ctx (Three l x m y t)

-------------------------------------------------------------------------------
-- Inserting
-------------------------------------------------------------------------------

insert : {{_ : Ord a}} -> a -> Tree a -> Tree a
insert {a} x = down []
  where
    up : List (TreeContext a) -> KickUp a -> Tree a
    up [] (KickUp: l x' r) = Two l x' r
    up (h :: ctx') kup with h | kup
    ... | TwoLeft x' r | KickUp: l z m =
      fromZipper ctx' (Three l z m x' r)
    ... | TwoRight l x' | KickUp: m z r =
      fromZipper ctx' (Three l x' m z r)
    ... | ThreeLeft x' c y d | KickUp: a z b =
      up ctx' (KickUp: (Two a z b) x' (Two c y d))
    ... | ThreeMiddle a x' y d | KickUp: b z c =
      up ctx' (KickUp: (Two a x' b) z (Two c y d))
    ... | ThreeRight a x' b y | KickUp: c z d =
      up ctx' (KickUp: (Two a x' b) y (Two c z d))

    down : List (TreeContext a) -> Tree a -> Tree a
    down ctx Leaf = up ctx (KickUp: Leaf x Leaf)
    down ctx (Two l y r) with compare x y
    ... | EQ = fromZipper ctx (Two l x r)
    ... | LT = down (TwoLeft y r :: ctx) l
    ... | GT = down (TwoRight l y :: ctx) r
    down ctx (Three l y m z r)
      with compare x y | compare x z
    ... | EQ | _ = fromZipper ctx (Three l x m z r)
    ... | _ | EQ = fromZipper ctx (Three l y m x r)
    ... | LT | _ = down (ThreeLeft y m z r :: ctx) l
    ... | GT | LT = down (ThreeMiddle l y z r :: ctx) m
    ... | _ | _ = down (ThreeRight l y m z :: ctx) r

-------------------------------------------------------------------------------
-- Deleting
-------------------------------------------------------------------------------

--delete : {{_ : Eq k}} -> k -> Tree a -> Tree a
--delete _ [] = []
--delete k (h :: t) = if fst h == k then t else delete k t

-------------------------------------------------------------------------------
-- Updating
-------------------------------------------------------------------------------

--adjust : {{_ : Eq k}} -> (v -> v) -> k -> Tree a -> Tree a
--adjust _ _ [] = []
--adjust f k (h :: t) =
--  if fst h == k
--  then (k , f (snd h)) :: t
--  else adjust f k t

-------------------------------------------------------------------------------
-- Querying
-------------------------------------------------------------------------------

--lookup : {{_ : Eq k}} -> k -> Tree a -> Maybe v
--lookup _ [] = Nothing
--lookup k (h :: t) = if fst h == k then Just (snd h) else lookup k t

--member : {{_ : Eq k}} -> k -> Tree a -> Bool
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
