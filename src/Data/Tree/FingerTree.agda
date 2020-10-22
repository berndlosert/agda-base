{-# OPTIONS --type-in-type #-}

module Data.Tree.FingerTree where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Data.Foldable
open import Data.Traversable

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b v : Set
    s t : Set -> Set

-------------------------------------------------------------------------------
-- Measured
-------------------------------------------------------------------------------

record Measured (v a : Set) : Set where
  field
    overlap {{Monoid-v}} : Monoid v
    measure : a -> v

open Measured {{...}} public

-------------------------------------------------------------------------------
-- Digit
-------------------------------------------------------------------------------

data Digit (a : Set) : Set where
  One : a -> Digit a
  Two : a -> a -> Digit a
  Three : a -> a -> a -> Digit a
  Four : a -> a -> a -> a -> Digit a

instance
  Foldable-Digit : Foldable Digit
  Foldable-Digit .foldMap f digit with digit
  ... | One a = f a
  ... | Two a b = f a <> f b
  ... | Three a b c = f a <> f b <> f c
  ... | Four a b c d = f a <> f b <> f c <> f d

  Functor-Digit : Functor Digit
  Functor-Digit .map f digit with digit
  ... | One a = One (f a)
  ... | Two a b = Two (f a) (f b)
  ... | Three a b c = Three (f a) (f b) (f c)
  ... | Four a b c d = Four (f a) (f b) (f c) (f d)

  Traversable-Digit : Traversable Digit
  Traversable-Digit .traverse f digit with digit
  ... | One a = (| One (f a) |)
  ... | Two a b = (| Two (f a) (f b) |)
  ... | Three a b c = (| Three (f a) (f b) (f c) |)
  ... | Four a b c d = (| Four (f a) (f b) (f c) (f d) |)

  Measured-Digit : {{_ : Measured v a}} -> Measured v (Digit a)
  Measured-Digit .measure = foldMap measure

-------------------------------------------------------------------------------
-- Node
-------------------------------------------------------------------------------

data Node (v a : Set) : Set where
  Node2 : v -> a -> a -> Node v a
  Node3 : v -> a -> a -> a -> Node v a

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

private
  node2 : {{_ : Measured v a}} -> a -> a -> Node v a
  node2 a b = Node2 (measure a <> measure b) a b

  node3 : {{_ : Measured v a}} -> a -> a -> a -> Node v a
  node3 a b c = Node3 (measure a <> measure b <> measure c) a b c

  nodeToDigit : Node v a -> Digit a
  nodeToDigit (Node2 _ a b) = Two a b
  nodeToDigit (Node3 _ a b c) = Three a b c

-------------------------------------------------------------------------------
-- FingerTree
-------------------------------------------------------------------------------

data FingerTree (v a : Set) : Set where
  Empty : FingerTree v a
  Single : a -> FingerTree v a
  Deep : v -> Digit a -> FingerTree v (Node v a) -> Digit a -> FingerTree v a

instance
  Measured-FingerTree : {{_ : Measured v a}} -> Measured v (FingerTree v a)
  Measured-FingerTree .measure tree with tree
  ... | Empty = mempty
  ... | Single x = measure x
  ... | Deep v _ _ _ = v

  Foldable-FingerTree : Foldable (FingerTree v)
  Foldable-FingerTree .foldMap f tree with tree
  ... | Empty = mempty
  ... | Single x = f x
  ... | Deep _ pr m sf = foldMap f pr <> foldMap (foldMap f) m <> foldMap f sf

  Functor-FingerTree : Functor (FingerTree v)
  Functor-FingerTree .map f tree with tree
  ... | Empty = Empty
  ... | Single x = Single (f x)
  ... | Deep v pr m sf = Deep v (map f pr) (map (map f) m) (map f sf)

  Traversable-FingerTree : Traversable (FingerTree v)
  Traversable-FingerTree .traverse f tree with tree
  ... | Empty = pure Empty
  ... | Single x = (| Single (f x) |)
  ... | (Deep v pr m sf) =
    (| (Deep v) (traverse f pr) (traverse (traverse f) m) (traverse f sf) |)

private
  deep : {{_ : Measured v a}}
    -> Digit a
    -> FingerTree v (Node v a)
    -> Digit a
    -> FingerTree v a
  deep pr m sf = Deep (measure pr <> measure m <> measure sf) pr m sf

  digitToTree : {{_ : Measured v a}} -> Digit a -> FingerTree v a
  digitToTree (One a) = Single a
  digitToTree (Two a b) = deep (One a) Empty (One b)
  digitToTree (Three a b c) = deep (Two a b) Empty (One c)
  digitToTree (Four a b c d) = deep (Two a b) Empty (Two c d)

-------------------------------------------------------------------------------
-- Cons operator
-------------------------------------------------------------------------------

infixr 5 _<|_
_<|_ : {{_ : Measured v a}} -> a -> FingerTree v a -> FingerTree v a

a <| Empty = Single a
a <| Single b = deep (One a) Empty (One b)
a <| Deep s (Four b c d e) m sf =
  Deep (measure a <> s) (Two a b) (node3 c d e <| m) sf
a <| (Deep s (Three b c d) m sf) =
  Deep (measure a <> s) (Four a b c d) m sf
a <| (Deep s (Two b c) m sf) =
  Deep (measure a <> s) (Three a b c) m sf
a <| (Deep s (One b) m sf) =
  Deep (measure a <> s) (Two a b) m sf

-------------------------------------------------------------------------------
-- Snoc operator
-------------------------------------------------------------------------------

infixl 5 _|>_
_|>_ : {{_ : Measured v a}} -> FingerTree v a -> a -> FingerTree v a

Empty |> a = Single a
Single a |>  b = deep (One a) Empty (One b)
Deep s pr m (Four a b c d) |> e =
  Deep (s <> measure e) pr (m |> node3 a b c) (Two d e)
Deep s pr m (Three a b c) |> d =
  Deep (s <> measure d) pr m (Four a b c d)
Deep s pr m (Two a b) |> c =
  Deep (s <> measure c) pr m (Three a b c)
Deep s pr m (One a) |> b =
  Deep (s <> measure b) pr m (Two a b)

-------------------------------------------------------------------------------
-- Semigroup & Monoid instances
-------------------------------------------------------------------------------

private

  -- Helpers (declarations)

  appendTree0 : {{_ : Measured v a}}
    -> FingerTree v a
    -> FingerTree v a
    -> FingerTree v a

  appendTree1 : {{_ : Measured v a}}
    -> FingerTree v a
    -> a
    -> FingerTree v a
    -> FingerTree v a

  appendTree2 : {{_ : Measured v a}}
    -> FingerTree v a
    -> a
    -> a
    -> FingerTree v a
    -> FingerTree v a

  appendTree3 : {{_ : Measured v a}}
    -> FingerTree v a
    -> a
    -> a
    -> a
    -> FingerTree v a
    -> FingerTree v a

  appendTree4 : {{_ : Measured v a}}
    -> FingerTree v a
    -> a
    -> a
    -> a
    -> a
    -> FingerTree v a
    -> FingerTree v a

  addDigits0 : {{_ : Measured v a}}
    -> FingerTree v (Node v a)
    -> Digit a
    -> Digit a
    -> FingerTree v (Node v a)
    -> FingerTree v (Node v a)

  addDigits1 : {{_ : Measured v a}}
    -> FingerTree v (Node v a)
    -> Digit a
    -> a
    -> Digit a
    -> FingerTree v (Node v a)
    -> FingerTree v (Node v a)

  addDigits2 : {{_ : Measured v a}}
    -> FingerTree v (Node v a)
    -> Digit a
    -> a
    -> a
     -> Digit a
    -> FingerTree v (Node v a)
    -> FingerTree v (Node v a)

  addDigits3 : {{_ : Measured v a}}
    -> FingerTree v (Node v a)
    -> Digit a
    -> a
    -> a
    -> a
    -> Digit a
    -> FingerTree v (Node v a)
    -> FingerTree v (Node v a)

  addDigits4 : {{_ : Measured v a}}
    -> FingerTree v (Node v a)
    -> Digit a
    -> a
    -> a
    -> a
    -> a
    -> Digit a
    -> FingerTree v (Node v a)
    -> FingerTree v (Node v a)

  -- Helpers (definitions)

  appendTree0 Empty xs = xs
  appendTree0 xs Empty = xs
  appendTree0 (Single x) xs = x <| xs
  appendTree0 xs (Single x) = xs |> x
  appendTree0 (Deep s1 pr1 m1 sf1) (Deep s2 pr2 m2 sf2) =
    deep pr1 (addDigits0 m1 sf1 pr2 m2) sf2

  appendTree1 Empty a xs = a <| xs
  appendTree1 xs a Empty = xs |> a
  appendTree1 (Single x) a xs = x <| a <| xs
  appendTree1 xs a (Single x) = xs |> a |> x
  appendTree1 (Deep s1 pr1 m1 sf1) a (Deep s2 pr2 m2 sf2) =
    deep pr1 (addDigits1 m1 sf1 a pr2 m2) sf2

  appendTree2 Empty a b xs = a <| b <| xs
  appendTree2 xs a b Empty = xs |> a |> b
  appendTree2 (Single x) a b xs = x <| a <| b <| xs
  appendTree2 xs a b (Single x) = xs |> a |> b |> x
  appendTree2 (Deep s1 pr1 m1 sf1) a b (Deep s2 pr2 m2 sf2) =
    deep pr1 (addDigits2 m1 sf1 a b pr2 m2) sf2

  appendTree3 Empty a b c xs = a <| b <| c <| xs
  appendTree3 xs a b c Empty = xs |> a |> b |> c
  appendTree3 (Single x) a b c xs = x <| a <| b <| c <| xs
  appendTree3 xs a b c (Single x) = xs |> a |> b |> c |> x
  appendTree3 (Deep s1 pr1 m1 sf1) a b c (Deep s2 pr2 m2 sf2) =
    deep pr1 (addDigits3 m1 sf1 a b c pr2 m2) sf2

  appendTree4 Empty a b c d xs = a <| b <| c <| d <| xs
  appendTree4 xs a b c d Empty = xs |> a |> b |> c |> d
  appendTree4 (Single x) a b c d xs = x <| a <| b <| c <| d <| xs
  appendTree4 xs a b c d (Single x) = xs |> a |> b |> c |> d |> x
  appendTree4 (Deep s1 pr1 m1 sf1) a b c d (Deep s2 pr2 m2 sf2) =
    deep pr1 (addDigits4 m1 sf1 a b c d pr2 m2) sf2

  addDigits0 m1 (One a) (One b) m2 =
    appendTree1 m1 (node2 a b) m2
  addDigits0 m1 (One a) (Two b c) m2 =
    appendTree1 m1 (node3 a b c) m2
  addDigits0 m1 (One a) (Three b c d) m2 =
    appendTree2 m1 (node2 a b) (node2 c d) m2
  addDigits0 m1 (One a) (Four b c d e) m2 =
    appendTree2 m1 (node3 a b c) (node2 d e) m2
  addDigits0 m1 (Two a b) (One c) m2 =
    appendTree1 m1 (node3 a b c) m2
  addDigits0 m1 (Two a b) (Two c d) m2 =
    appendTree2 m1 (node2 a b) (node2 c d) m2
  addDigits0 m1 (Two a b) (Three c d e) m2 =
    appendTree2 m1 (node3 a b c) (node2 d e) m2
  addDigits0 m1 (Two a b) (Four c d e f) m2 =
    appendTree2 m1 (node3 a b c) (node3 d e f) m2
  addDigits0 m1 (Three a b c) (One d) m2 =
    appendTree2 m1 (node2 a b) (node2 c d) m2
  addDigits0 m1 (Three a b c) (Two d e) m2 =
    appendTree2 m1 (node3 a b c) (node2 d e) m2
  addDigits0 m1 (Three a b c) (Three d e f) m2 =
    appendTree2 m1 (node3 a b c) (node3 d e f) m2
  addDigits0 m1 (Three a b c) (Four d e f g) m2 =
    appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
  addDigits0 m1 (Four a b c d) (One e) m2 =
    appendTree2 m1 (node3 a b c) (node2 d e) m2
  addDigits0 m1 (Four a b c d) (Two e f) m2 =
    appendTree2 m1 (node3 a b c) (node3 d e f) m2
  addDigits0 m1 (Four a b c d) (Three e f g) m2 =
    appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
  addDigits0 m1 (Four a b c d) (Four e f g h) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2

  addDigits1 m1 (One a) b (One c) m2 =
    appendTree1 m1 (node3 a b c) m2
  addDigits1 m1 (One a) b (Two c d) m2 =
    appendTree2 m1 (node2 a b) (node2 c d) m2
  addDigits1 m1 (One a) b (Three c d e) m2 =
    appendTree2 m1 (node3 a b c) (node2 d e) m2
  addDigits1 m1 (One a) b (Four c d e f) m2 =
    appendTree2 m1 (node3 a b c) (node3 d e f) m2
  addDigits1 m1 (Two a b) c (One d) m2 =
    appendTree2 m1 (node2 a b) (node2 c d) m2
  addDigits1 m1 (Two a b) c (Two d e) m2 =
    appendTree2 m1 (node3 a b c) (node2 d e) m2
  addDigits1 m1 (Two a b) c (Three d e f) m2 =
    appendTree2 m1 (node3 a b c) (node3 d e f) m2
  addDigits1 m1 (Two a b) c (Four d e f g) m2 =
    appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
  addDigits1 m1 (Three a b c) d (One e) m2 =
    appendTree2 m1 (node3 a b c) (node2 d e) m2
  addDigits1 m1 (Three a b c) d (Two e f) m2 =
    appendTree2 m1 (node3 a b c) (node3 d e f) m2
  addDigits1 m1 (Three a b c) d (Three e f g) m2 =
    appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
  addDigits1 m1 (Three a b c) d (Four e f g h) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
  addDigits1 m1 (Four a b c d) e (One f) m2 =
    appendTree2 m1 (node3 a b c) (node3 d e f) m2
  addDigits1 m1 (Four a b c d) e (Two f g) m2 =
    appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
  addDigits1 m1 (Four a b c d) e (Three f g h) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
  addDigits1 m1 (Four a b c d) e (Four f g h i) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2

  addDigits2 m1 (One a) b c (One d) m2 =
    appendTree2 m1 (node2 a b) (node2 c d) m2
  addDigits2 m1 (One a) b c (Two d e) m2 =
    appendTree2 m1 (node3 a b c) (node2 d e) m2
  addDigits2 m1 (One a) b c (Three d e f) m2 =
    appendTree2 m1 (node3 a b c) (node3 d e f) m2
  addDigits2 m1 (One a) b c (Four d e f g) m2 =
    appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
  addDigits2 m1 (Two a b) c d (One e) m2 =
    appendTree2 m1 (node3 a b c) (node2 d e) m2
  addDigits2 m1 (Two a b) c d (Two e f) m2 =
    appendTree2 m1 (node3 a b c) (node3 d e f) m2
  addDigits2 m1 (Two a b) c d (Three e f g) m2 =
    appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
  addDigits2 m1 (Two a b) c d (Four e f g h) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
  addDigits2 m1 (Three a b c) d e (One f) m2 =
    appendTree2 m1 (node3 a b c) (node3 d e f) m2
  addDigits2 m1 (Three a b c) d e (Two f g) m2 =
    appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
  addDigits2 m1 (Three a b c) d e (Three f g h) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
  addDigits2 m1 (Three a b c) d e (Four f g h i) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
  addDigits2 m1 (Four a b c d) e f (One g) m2 =
    appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
  addDigits2 m1 (Four a b c d) e f (Two g h) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
  addDigits2 m1 (Four a b c d) e f (Three g h i) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
  addDigits2 m1 (Four a b c d) e f (Four g h i j) m2 =
    appendTree4 m1 (node3 a b c) (node3 d e f) (node2 g h) (node2 i j) m2

  addDigits3 m1 (One a) b c d (One e) m2 =
      appendTree2 m1 (node3 a b c) (node2 d e) m2
  addDigits3 m1 (One a) b c d (Two e f) m2 =
      appendTree2 m1 (node3 a b c) (node3 d e f) m2
  addDigits3 m1 (One a) b c d (Three e f g) m2 =
      appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
  addDigits3 m1 (One a) b c d (Four e f g h) m2 =
      appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
  addDigits3 m1 (Two a b) c d e (One f) m2 =
      appendTree2 m1 (node3 a b c) (node3 d e f) m2
  addDigits3 m1 (Two a b) c d e (Two f g) m2 =
      appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
  addDigits3 m1 (Two a b) c d e (Three f g h) m2 =
      appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
  addDigits3 m1 (Two a b) c d e (Four f g h i) m2 =
      appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
  addDigits3 m1 (Three a b c) d e f (One g) m2 =
      appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
  addDigits3 m1 (Three a b c) d e f (Two g h) m2 =
      appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
  addDigits3 m1 (Three a b c) d e f (Three g h i) m2 =
      appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
  addDigits3 m1 (Three a b c) d e f (Four g h i j) m2 =
      appendTree4 m1 (node3 a b c) (node3 d e f) (node2 g h) (node2 i j) m2
  addDigits3 m1 (Four a b c d) e f g (One h) m2 =
      appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
  addDigits3 m1 (Four a b c d) e f g (Two h i) m2 =
      appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
  addDigits3 m1 (Four a b c d) e f g (Three h i j) m2 =
      appendTree4 m1 (node3 a b c) (node3 d e f) (node2 g h) (node2 i j) m2
  addDigits3 m1 (Four a b c d) e f g (Four h i j k) m2 =
      appendTree4 m1 (node3 a b c) (node3 d e f) (node3 g h i) (node2 j k) m2

  addDigits4 m1 (One a) b c d e (One f) m2 =
    appendTree2 m1 (node3 a b c) (node3 d e f) m2
  addDigits4 m1 (One a) b c d e (Two f g) m2 =
    appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
  addDigits4 m1 (One a) b c d e (Three f g h) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
  addDigits4 m1 (One a) b c d e (Four f g h i) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
  addDigits4 m1 (Two a b) c d e f (One g) m2 =
    appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
  addDigits4 m1 (Two a b) c d e f (Two g h) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
  addDigits4 m1 (Two a b) c d e f (Three g h i) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
  addDigits4 m1 (Two a b) c d e f (Four g h i j) m2 =
    appendTree4 m1 (node3 a b c) (node3 d e f) (node2 g h) (node2 i j) m2
  addDigits4 m1 (Three a b c) d e f g (One h) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
  addDigits4 m1 (Three a b c) d e f g (Two h i) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
  addDigits4 m1 (Three a b c) d e f g (Three h i j) m2 =
    appendTree4 m1 (node3 a b c) (node3 d e f) (node2 g h) (node2 i j) m2
  addDigits4 m1 (Three a b c) d e f g (Four h i j k) m2 =
    appendTree4 m1 (node3 a b c) (node3 d e f) (node3 g h i) (node2 j k) m2
  addDigits4 m1 (Four a b c d) e f g h (One i) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
  addDigits4 m1 (Four a b c d) e f g h (Two i j) m2 =
    appendTree4 m1 (node3 a b c) (node3 d e f) (node2 g h) (node2 i j) m2
  addDigits4 m1 (Four a b c d) e f g h (Three i j k) m2 =
    appendTree4 m1 (node3 a b c) (node3 d e f) (node3 g h i) (node2 j k) m2
  addDigits4 m1 (Four a b c d) e f g h (Four i j k l) m2 =
    appendTree4 m1 (node3 a b c) (node3 d e f) (node3 g h i) (node3 j k l) m2

-- Finally...

instance
  Semigroup-FingerTree : {{_ : Measured v a}} -> Semigroup (FingerTree v a)
  Semigroup-FingerTree ._<>_ = appendTree0

  Monoid-FingerTree : {{_ : Measured v a}} -> Monoid (FingerTree v a)
  Monoid-FingerTree .mempty = Empty

-------------------------------------------------------------------------------
-- ViewL & ViewR
-------------------------------------------------------------------------------

infixr 5 _:<_
data ViewL (s : Set -> Set) (a : Set) : Set where
  EmptyL : ViewL s a
  _:<_ : a -> s a -> ViewL s a

infixr 5 _:>_
data ViewR (s : Set -> Set) (a : Set) : Set where
  EmptyR : ViewR s a
  _:>_ : s a -> a -> ViewR s a

instance
  Functor-ViewL : {{_ : Functor s}} -> Functor (ViewL s)
  Functor-ViewL .map _ EmptyL = EmptyL
  Functor-ViewL .map f (x :< xs) = f x :< map f xs

  Functor-ViewR : {{_ : Functor s}} -> Functor (ViewR s)
  Functor-ViewR .map _ EmptyR = EmptyR
  Functor-ViewR .map f (xs :> x) = map f xs :> f x

viewl : {{_ : Measured v a}}
  -> FingerTree v a
  -> ViewL (FingerTree v) a

private
  rotL : {{_ : Measured v a}}
    -> FingerTree v (Node v a)
    -> Digit a
    -> FingerTree v a

viewl Empty = EmptyL
viewl (Single x) = x :< Empty
viewl (Deep _ (One x) m sf) = x :< rotL m sf
viewl (Deep _ (Two a b) m sf) = a :< deep (One b) m sf
viewl (Deep _ (Three a b c) m sf) = a :< deep (Two b c) m sf
viewl (Deep _ (Four a b c d) m sf) = a :< deep (Three b c d) m sf

rotL m sf with viewl m
... | EmptyL = digitToTree sf
... | a :< m' = Deep (measure m <> measure sf) (nodeToDigit a) m' sf
