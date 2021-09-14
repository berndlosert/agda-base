{-# OPTIONS --type-in-type #-}

module Data.Tree.Finger.Node where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Data.Tree.Finger.Digit
open import Data.Tree.Finger.Measured
open import Data.Tree.Finger.Split
open import Data.Foldable
open import Data.Traversable

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b s v : Set

-------------------------------------------------------------------------------
-- Node
-------------------------------------------------------------------------------

data Node (v a : Set) : Set where
  node2 : v -> a -> a -> Node v a
  node3 : v -> a -> a -> a -> Node v a

node2' : {{Measured v a}} -> a -> a -> Node v a
node2' a b = node2 (measure a <> measure b) a b

node3' : {{Measured v a}} -> a -> a -> a -> Node v a
node3' a b c = node3 (measure a <> measure b <> measure c) a b c

nodeToDigit : Node v a -> Digit a
nodeToDigit (node2 _ a b) = two a b
nodeToDigit (node3 _ a b c) = three a b c

nodes : {{Measured v a}} -> List a -> List (Node v a)
nodes (a :: b :: []) = node2' a b :: []
nodes (a :: b :: c :: []) = node3' a b c :: []
nodes (a :: b :: c :: d :: []) = node2' a b :: node2' c d :: []
nodes (a :: b :: c :: xs) = node3' a b c :: nodes xs
nodes _ = []

instance
  Foldable-Node : Foldable (Node v)
  Foldable-Node .foldr f z = \ where
    (node2 _ a b) -> f a (f b z)
    (node3 _ a b c) -> f a (f b (f c z))

  Functor-Node : Functor (Node v)
  Functor-Node .map f = \ where
    (node2 v a b) -> node2 v (f a) (f b)
    (node3 v a b c) -> node3 v (f a) (f b) (f c)

  Traversable-Node : Traversable (Node v)
  Traversable-Node .traverse f = \ where
    (node2 v a b) -> (| (node2 v) (f a) (f b) |)
    (node3 v a b c) -> (| (node3 v) (f a) (f b) (f c) |)

  Measured-Node : {{Monoid v}} -> Measured v (Node v a)
  Measured-Node .measure (node2 v _ _) = v
  Measured-Node .measure (node3 v _ _ _) = v

-------------------------------------------------------------------------------
-- Splitting
-------------------------------------------------------------------------------

splitNode : {{Measured v a}}
  -> (v -> Bool)
  -> v
  -> Node v a
  -> Split (Maybe <<< Digit) a
splitNode p i (node2 _ a b) =
  let
    va = i <> measure a
  in
    if p va then toSplit nothing a (just (one b))
    else toSplit (just (one a)) b nothing
splitNode p i (node3 _ a b c) =
  let
    va = i <> measure a
    vab = va <> measure b
  in
    if p va then toSplit nothing a (just (two b c))
    else if p vab then toSplit (just (one a)) b (just (one c))
    else toSplit (just (two a b)) c nothing

-------------------------------------------------------------------------------
-- Searching
-------------------------------------------------------------------------------

searchNode : {{Measured v a}}
  -> (v -> v -> Bool)
  -> v
  -> Node v a
  -> v
  -> Split (Maybe <<< Digit) a
searchNode p vl (node2 _ a b) vr =
  let
    va = vl <> measure a
    vb = measure b <> vr
  in
    if p va vb then toSplit nothing a (just (one b))
    else toSplit (just (one a)) b nothing
searchNode p vl (node3 _ a b c) vr =
  let
    va = vl <> measure a
    vab = va <> measure b
    vc = measure c <> vr
    vbc = measure b <> vc
  in
    if p va vbc then toSplit nothing a (just (two b c))
    else if p vab vc then toSplit (just (one a)) b (just (one c))
    else toSplit (just (two a b)) c nothing

-------------------------------------------------------------------------------
-- Misc.
-------------------------------------------------------------------------------

initsNode : Node v a -> Node v (Digit a)
initsNode (node2 v a b) = node2 v (one a) (two a b)
initsNode (node3 v a b c) = node3 v (one a) (two a b) (three a b c)

tailsNode : Node v a -> Node v (Digit a)
tailsNode (node2 v a b) = node2 v (two a b) (one b)
tailsNode (node3 v a b c) = node3 v (three a b c) (two b c) (one c)

splitMapNode : {{Measured v a}}
  -> (v -> s -> Pair s s)
  -> (s -> a -> b)
  -> s -> Node v a -> Node v b
splitMapNode split f s (node2 ns a b) =
  let (first , second) = split (measure a) s
  in node2 ns (f first a) (f second b)
splitMapNode split f s (node3 ns a b c) =
  let
    (first , r) = split (measure a) s
    (second , third) = split (measure b) r
  in
    node3 ns (f first a) (f second b) (f third c)
