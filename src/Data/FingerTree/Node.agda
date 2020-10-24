{-# OPTIONS --type-in-type #-}

module Data.FingerTree.Node where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Data.FingerTree.Digit
open import Data.FingerTree.Measured
open import Data.Foldable
open import Data.Traversable

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a v : Set

-------------------------------------------------------------------------------
-- Node
-------------------------------------------------------------------------------

data Node (v a : Set) : Set where
  Node2 : v -> a -> a -> Node v a
  Node3 : v -> a -> a -> a -> Node v a

node2 : {{_ : Measured v a}} -> a -> a -> Node v a
node2 a b = Node2 (measure a <> measure b) a b

node3 : {{_ : Measured v a}} -> a -> a -> a -> Node v a
node3 a b c = Node3 (measure a <> measure b <> measure c) a b c

nodeToDigit : Node v a -> Digit a
nodeToDigit (Node2 _ a b) = Two a b
nodeToDigit (Node3 _ a b c) = Three a b c

nodes : {{_ : Measured v a}} -> List a -> List (Node v a)
nodes (a :: b :: []) = [ node2 a b ]
nodes (a :: b :: c :: []) = [ node3 a b c ]
nodes (a :: b :: c :: d :: []) = node2 a b :: node2 c d :: []
nodes (a :: b :: c :: xs) = node3 a b c :: nodes xs
nodes _ = []

instance
  Foldable-Node : Foldable (Node v)
  Foldable-Node .foldMap f node with node
  ... | Node2 _ a b = f a <> f b
  ... | Node3 _ a b c = f a <> f b <> f c

  Functor-Node : Functor (Node v)
  Functor-Node .map f node with node
  ... | Node2 v a b = Node2 v (f a) (f b)
  ... | Node3 v a b c = Node3 v (f a) (f b) (f c)

  Traversable-Node : Traversable (Node v)
  Traversable-Node .traverse f node with node
  ... | Node2 v a b = (| (Node2 v) (f a) (f b) |)
  ... | Node3 v a b c = (| (Node3 v) (f a) (f b) (f c) |)

  Measured-Node : {{_ : Monoid v}} -> Measured v (Node v a)
  Measured-Node .measure (Node2 v _ _) = v
  Measured-Node .measure (Node3 v _ _ _) = v

-------------------------------------------------------------------------------
-- Splitting
-------------------------------------------------------------------------------

splitNode : {{_ : Measured v a}}
  -> (v -> Bool)
  -> v
  -> Node v a
  -> Maybe (Digit a) * a * Maybe (Digit a)
splitNode p i (Node2 _ a b) =
  let
    va = i <> measure a
  in
    if p va then (Nothing , a , Just (One b))
    else (Just (One a) , b , Nothing)
splitNode p i (Node3 _ a b c) =
  let
    va = i <> measure a
    vab = va <> measure b
  in
    if p va then (Nothing , a , Just (Two b c))
    else if p vab then (Just (One a) , b , Just (One c))
    else (Just (Two a b) , c , Nothing)

-------------------------------------------------------------------------------
-- Searching
-------------------------------------------------------------------------------

searchNode : {{_ : Measured v a}}
  -> (v -> v -> Bool)
  -> v
  -> Node v a
  -> v
  -> Maybe (Digit a) * a * Maybe (Digit a)
searchNode p vl (Node2 _ a b) vr =
  let
    va = vl <> measure a
    vb = measure b <> vr
  in
    if p va vb then (Nothing , a , Just (One b))
    else (Just (One a) , b , Nothing)
searchNode p vl (Node3 _ a b c) vr =
  let
    va = vl <> measure a
    vab = va <> measure b
    vc = measure c <> vr
    vbc = measure b <> vc
  in
    if p va vbc then (Nothing , a , Just (Two b c))
    else if p vab vc then (Just (One a) , b , Just (One c))
    else (Just (Two a b) , c , Nothing)
