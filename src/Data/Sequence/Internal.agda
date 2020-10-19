{-# OPTIONS --type-in-type #-}

module Data.Sequence.Internal where

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
    a b : Set
    t : Set -> Set

-------------------------------------------------------------------------------
-- Sized
-------------------------------------------------------------------------------

record Sized (a : Set) : Set where
  field size : a -> Nat

open Sized {{...}} public

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

  Sized-Digit : {{_ : Sized a}} -> Sized (Digit a)
  Sized-Digit .size = sum <<< map size

-------------------------------------------------------------------------------
-- Node
-------------------------------------------------------------------------------

data Node (a : Set) : Set where
  Node2 : Nat -> a -> a -> Node a
  Node3 : Nat -> a -> a -> a -> Node a

node2 : {{_ : Sized a}} -> a -> a -> Node a
node2 a b = Node2 (size a + size b) a b

node3 : {{_ : Sized a}} -> a -> a -> a -> Node a
node3 a b c = Node3 (size a + size b + size c) a b c

instance
  Foldable-Node : Foldable Node
  Foldable-Node .foldMap f node with node
  ... | Node2 _ a b = f a <> f b
  ... | Node3 _ a b c = f a <> f b <> f c

  Functor-Node : Functor Node
  Functor-Node .map f node with node
  ... | Node2 v a b = Node2 v (f a) (f b)
  ... | Node3 v a b c = Node3 v (f a) (f b) (f c)

  Traversable-Node : Traversable Node
  Traversable-Node .traverse f node with node
  ... | Node2 v a b = (| (Node2 v) (f a) (f b) |)
  ... | Node3 v a b c = (| (Node3 v) (f a) (f b) (f c) |)

  Sized-Node : Sized (Node a)
  Sized-Node .size (Node2 v _ _) = v
  Sized-Node .size (Node3 v _ _ _) = v

-------------------------------------------------------------------------------
-- FingerTree
-------------------------------------------------------------------------------

data FingerTree (a : Set) : Set where
  Empty : FingerTree a
  Single : a -> FingerTree a
  Deep : Nat -> Digit a -> FingerTree (Node a) -> Digit a -> FingerTree a

instance
  Sized-FingerTree : {{_ : Sized a}} -> Sized (FingerTree a)
  Sized-FingerTree .size tree with tree
  ... | Empty = 0
  ... | Single x = size x
  ... | Deep v _ _ _ = v

  Foldable-FingerTree : Foldable FingerTree
  Foldable-FingerTree .foldMap f tree with tree
  ... | Empty = mempty
  ... | Single x = f x
  ... | Deep _ pr m sf = foldMap f pr <> foldMap (foldMap f) m <> foldMap f sf

  Functor-FingerTree : Functor FingerTree
  Functor-FingerTree .map f tree with tree
  ... | Empty = Empty
  ... | Single x = Single (f x)
  ... | Deep v pr m sf = Deep v (map f pr) (map (map f) m) (map f sf)

  Traversable-FingerTree : Traversable FingerTree
  Traversable-FingerTree .traverse f tree with tree
  ... | Empty = pure Empty
  ... | Single x = (| Single (f x) |)
  ... | (Deep v pr m sf) =
    (| (Deep v) (traverse f pr) (traverse (traverse f) m) (traverse f sf) |)

deep : {{_ : Sized a}} -> Digit a -> FingerTree (Node a) -> Digit a
  -> FingerTree a
deep pr m sf = Deep (size pr + size m + size sf) pr m sf

-------------------------------------------------------------------------------
-- Elem
-------------------------------------------------------------------------------

record Elem (a : Set) : Set where
  constructor Elem:
  field getElem : a

open Elem public

instance
  Sized-Elem : Sized (Elem a)
  Sized-Elem .size _ = 1

  Functor-Elem : Functor Elem
  Functor-Elem .map f (Elem: x) = Elem: (f x)

  Foldable-Elem : Foldable Elem
  Foldable-Elem .foldMap f (Elem: x) = f x

  Traversable-Elem : Traversable Elem
  Traversable-Elem .traverse f (Elem: x) = (| Elem: (f x) |)

-------------------------------------------------------------------------------
-- traverseNE & traveseDE helpers
-------------------------------------------------------------------------------

traverseNE : {{_ : Applicative t}}
  -> (a -> t b) -> Node (Elem a) -> t (Node (Elem b))
traverseNE g node with node
... | Node2 v (Elem: a) (Elem: b) =
  (| (\ x y -> Node2 v (Elem: x) (Elem: y)) (g a) (g b) |)
... | Node3 v (Elem: a) (Elem: b) (Elem: c) =
  (| (\ x y z -> Node3 v (Elem: x) (Elem: y) (Elem: z)) (g a) (g b) (g c) |)

traverseDE : {{_ : Applicative t}}
  -> (a -> t b) -> Digit (Elem a) -> t (Digit (Elem b))
traverseDE g digit with digit
... | One (Elem: a) =
  (| (\ x -> One (Elem: x)) (g a) |)
... | Two (Elem: a) (Elem: b) =
  (| (\ x y -> Two (Elem: x) (Elem: y)) (g a) (g b) |)
... | Three (Elem: a) (Elem: b) (Elem: c) =
  (| (\ x y z -> Three (Elem: x) (Elem: y) (Elem: z)) (g a) (g b) (g c) |)
... | Four (Elem: a) (Elem: b) (Elem: c) (Elem: d) =
  (| (\ w x y z -> Four (Elem: w) (Elem: x) (Elem: y) (Elem: z)) (g a) (g b) (g c) (g d) |)

-------------------------------------------------------------------------------
-- consTree
-------------------------------------------------------------------------------

consTree : {{_ : Sized a}} -> a -> FingerTree a -> FingerTree a
consTree a Empty = Single a
consTree a (Single b) = deep (One a) Empty (One b)
consTree a (Deep s (Four b c d e) m sf) =
  Deep (size a + s) (Two a b) (consTree (node3 c d e) m) sf
consTree a (Deep s (Three b c d) m sf) =
  Deep (size a + s) (Four a b c d) m sf
consTree a (Deep s (Two b c) m sf) =
  Deep (size a + s) (Three a b c) m sf
consTree a (Deep s (One b) m sf) =
  Deep (size a + s) (Two a b) m sf

infixr 5 _<|_
_<|_ : {{_ : Sized a}} -> a -> FingerTree a -> FingerTree a
_<|_ = consTree

-------------------------------------------------------------------------------
-- snocTree
-------------------------------------------------------------------------------

snocTree : {{_ : Sized a}} -> FingerTree a -> a -> FingerTree a
snocTree Empty a = Single a
snocTree (Single a) b = deep (One a) Empty (One b)
snocTree (Deep s pr m (Four a b c d)) e =
  Deep (s + size e) pr (snocTree m (node3 a b c)) (Two d e)
snocTree (Deep s pr m (Three a b c)) d =
  Deep (s + size d) pr m (Four a b c d)
snocTree (Deep s pr m (Two a b)) c =
  Deep (s + size c) pr m (Three a b c)
snocTree (Deep s pr m (One a)) b =
  Deep (s + size b) pr m (Two a b)

infixl 5 _|>_
_|>_ : {{_ : Sized a}} -> FingerTree a -> a -> FingerTree a
_|>_ = snocTree

-------------------------------------------------------------------------------
-- appendTree & addDigits helpers
-------------------------------------------------------------------------------

-- Helper functions (declarations)

appendTree0 : FingerTree (Elem a)
  -> FingerTree (Elem a)
  -> FingerTree (Elem a)

appendTree1 : FingerTree (Node a)
  -> Node a
  -> FingerTree (Node a)
  -> FingerTree (Node a)

appendTree2 : FingerTree (Node a)
  -> Node a
  -> Node a
  -> FingerTree (Node a)
  -> FingerTree (Node a)

appendTree3 : FingerTree (Node a)
  -> Node a
  -> Node a
  -> Node a
  -> FingerTree (Node a)
  -> FingerTree (Node a)

appendTree4 : FingerTree (Node a)
  -> Node a
  -> Node a
  -> Node a
  -> Node a
  -> FingerTree (Node a)
  -> FingerTree (Node a)

addDigits0 : FingerTree (Node (Elem a))
  -> Digit (Elem a)
  -> Digit (Elem a)
  -> FingerTree (Node (Elem a))
  -> FingerTree (Node (Elem a))

addDigits1 : FingerTree (Node (Node a))
  -> Digit (Node a)
  -> Node a
  -> Digit (Node a)
  -> FingerTree (Node (Node a))
  -> FingerTree (Node (Node a))

addDigits2 : FingerTree (Node (Node a))
  -> Digit (Node a)
  -> Node a
  -> Node a
  -> Digit (Node a)
  -> FingerTree (Node (Node a))
  -> FingerTree (Node (Node a))

addDigits3 : FingerTree (Node (Node a))
  -> Digit (Node a)
  -> Node a
  -> Node a
  -> Node a
  -> Digit (Node a)
  -> FingerTree (Node (Node a))
  -> FingerTree (Node (Node a))

addDigits4 : FingerTree (Node (Node a))
  -> Digit (Node a)
  -> Node a
  -> Node a
  -> Node a
  -> Node a
  -> Digit (Node a)
  -> FingerTree (Node (Node a))
  -> FingerTree (Node (Node a))

-- Helper functions (definitions)

appendTree0 Empty xs = xs
appendTree0 xs Empty = xs
appendTree0 (Single x) xs = x <| xs
appendTree0 xs (Single x) = xs |> x
appendTree0 (Deep s1 pr1 m1 sf1) (Deep s2 pr2 m2 sf2) =
  let m = addDigits0 m1 sf1 pr2 m2
  in Deep (s1 + s2) pr1 m sf2

appendTree1 Empty a xs = a <| xs
appendTree1 xs a Empty = xs |> a
appendTree1 (Single x) a xs = x <| a <| xs
appendTree1 xs a (Single x) = xs |> a |> x
appendTree1 (Deep s1 pr1 m1 sf1) a (Deep s2 pr2 m2 sf2) =
  let m = addDigits1 m1 sf1 a pr2 m2
  in Deep (s1 + size a + s2) pr1 m sf2

appendTree2 Empty a b xs = a <| b <| xs
appendTree2 xs a b Empty = xs |> a |> b
appendTree2 (Single x) a b xs = x <| a <| b <| xs
appendTree2 xs a b (Single x) = xs |> a |> b |> x
appendTree2 (Deep s1 pr1 m1 sf1) a b (Deep s2 pr2 m2 sf2) =
  let m = addDigits2 m1 sf1 a b pr2 m2
  in Deep (s1 + size a + size b + s2) pr1 m sf2

appendTree3 Empty a b c xs = a <| b <| c <| xs
appendTree3 xs a b c Empty = xs |> a |> b |> c
appendTree3 (Single x) a b c xs = x <| a <| b <| c <| xs
appendTree3 xs a b c (Single x) = xs |> a |> b |> c |> x
appendTree3 (Deep s1 pr1 m1 sf1) a b c (Deep s2 pr2 m2 sf2) =
  let m = addDigits3 m1 sf1 a b c pr2 m2
  in Deep (s1 + size a + size b + size c + s2) pr1 m sf2

appendTree4 Empty a b c d xs = a <| b <| c <| d <| xs
appendTree4 xs a b c d Empty = xs |> a |> b |> c |> d
appendTree4 (Single x) a b c d xs = x <| a <| b <| c <| d <| xs
appendTree4 xs a b c d (Single x) = xs |> a |> b |> c |> d |> x
appendTree4 (Deep s1 pr1 m1 sf1) a b c d (Deep s2 pr2 m2 sf2) =
  let m = addDigits4 m1 sf1 a b c d pr2 m2
  in Deep (s1 + size a + size b + size c + size d + s2) pr1 m sf2

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

-------------------------------------------------------------------------------
-- apSeq
-------------------------------------------------------------------------------
{-
apSeq : Seq (a -> b) -> Seq a -> Seq b
apSeq: fs xs@(Seq: xsFT) = case viewl fs of
  EmptyL -> empty
  firstf :< fs' -> case viewr fs' of
    EmptyR -> map firstf xs
    Seq: fs''FT :> lastf -> case rigidify xsFT of
      RigidEmpty -> empty
      RigidOne (Elem x) -> flap fs x
      RigidTwo (Elem x1) (Elem x2) ->
         Seq: $ ap2FT firstf fs''FT lastf (x1, x2)
      RigidThree (Elem x1) (Elem x2) (Elem x3) ->
         Seq: $ ap3FT firstf fs''FT lastf (x1, x2, x3)
      RigidFull r@(Rigid s pr _m sf) -> Seq: $
        Deep (s * length fs)
          (map (map firstf) (nodeToDigit pr))
          (liftA2Middle (map firstf) (map lastf) map fs''FT r)
          (map (map lastf) (nodeToDigit sf))
-}
