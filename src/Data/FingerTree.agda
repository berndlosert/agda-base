{-# OPTIONS --type-in-type #-}

module Data.FingerTree where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Data.Constraint.Nonempty
open import Data.Foldable
open import Data.Sequence.View
open import Data.Traversable
open import Data.FingerTree.Digit
open import Data.FingerTree.Measured
open import Data.FingerTree.Node

-------------------------------------------------------------------------------
-- Re-exports
-------------------------------------------------------------------------------

open Data.Sequence.View public

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b v : Set
    s t : Set -> Set

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

  NonemptyConstraint-FingerTree : NonemptyConstraint (FingerTree v a)
  NonemptyConstraint-FingerTree .IsNonempty Empty = Void
  NonemptyConstraint-FingerTree .IsNonempty _ = Unit

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
-- viewl & viewr
-------------------------------------------------------------------------------

viewl : {{_ : Measured v a}}
  -> FingerTree v a
  -> ViewL (FingerTree v) a

viewr : {{_ : Measured v a}}
  -> FingerTree v a
  -> ViewR (FingerTree v) a

private
  rotL : {{_ : Measured v a}}
    -> FingerTree v (Node v a)
    -> Digit a
    -> FingerTree v a

  rotR : {{_ : Measured v a}}
    -> Digit a
    -> FingerTree v (Node v a)
    -> FingerTree v a

viewl Empty = EmptyL
viewl (Single x) = x :< Empty
viewl (Deep _ (One x) m sf) = x :< rotL m sf
viewl (Deep _ (Two a b) m sf) = a :< deep (One b) m sf
viewl (Deep _ (Three a b c) m sf) = a :< deep (Two b c) m sf
viewl (Deep _ (Four a b c d) m sf) = a :< deep (Three b c d) m sf

viewr Empty = EmptyR
viewr (Single x) = Empty :> x
viewr (Deep _ pr m (One x)) = rotR pr m :> x
viewr (Deep _ pr m (Two a b)) = deep pr m (One a) :> b
viewr (Deep _ pr m (Three a b c)) = deep pr m (Two a b) :> c
viewr (Deep _ pr m (Four a b c d)) = deep pr m (Three a b c) :> d

rotL m sf with viewl m
... | EmptyL = digitToTree sf
... | a :< m' = Deep (measure m <> measure sf) (nodeToDigit a) m' sf

rotR pr m with viewr m
... | EmptyR = digitToTree pr
... | m' :> a = Deep (measure pr <> measure m) pr m' (nodeToDigit a)

-------------------------------------------------------------------------------
-- split
-------------------------------------------------------------------------------

private
  data Split (t a : Set) : Set where
    Split: : t -> a -> t -> Split t a

  splitDigit : {{_ : Measured v a }}
    -> (v -> Bool)
    -> v
    -> Digit a
    -> Split (Maybe (Digit a)) a
  splitDigit _ i (One a) = Split: Nothing a Nothing
  splitDigit p i (Two a b) =
    let
      va = i <> measure a
    in
      if p va then Split: Nothing a (Just (One b))
      else Split: (Just (One a)) b Nothing
  splitDigit p i (Three a b c) =
    let
      va = i <> measure a
      vab = va <> measure b
    in
      if p va then Split: Nothing a (Just (Two b c))
      else if p vab then Split: (Just (One a)) b (Just (One c))
      else Split: (Just (Two a b)) c Nothing
  splitDigit p i (Four a b c d) =
    let
      va = i <> measure a
      vab = va <> measure b
      vabc = vab <> measure c
    in
      if p va then Split: Nothing a (Just (Three b c d))
      else if p vab then Split: (Just (One a)) b (Just (Two c d))
      else if p vabc then Split: (Just (Two a b)) c (Just (One d))
      else Split: (Just (Three a b c)) d Nothing

  splitNode : {{_ : Measured v a}}
    -> (v -> Bool)
    -> v
    -> Node v a
    -> Split (Maybe (Digit a)) a
  splitNode p i (Node2 _ a b) =
    let
      va = i <> measure a
    in
      if p va then Split: Nothing a (Just (One b))
      else Split: (Just (One a)) b Nothing
  splitNode p i (Node3 _ a b c) =
    let
      va = i <> measure a
      vab = va <> measure b
    in
      if p va then Split: Nothing a (Just (Two b c))
      else if p vab then Split: (Just (One a)) b (Just (One c))
      else Split: (Just (Two a b)) c Nothing

  deepL : {{_ : Measured v a}}
    -> Maybe (Digit a)
    -> FingerTree v (Node v a)
    -> Digit a
    -> FingerTree v a
  deepL Nothing m sf = rotL m sf
  deepL (Just pr) m sf = deep pr m sf

  deepR : {{_ : Measured v a}}
    -> Digit a
    -> FingerTree v (Node v a)
    -> Maybe (Digit a)
    -> FingerTree v a
  deepR pr m Nothing = rotR pr m
  deepR pr m (Just sf) =  deep pr m sf

  splitTree : {{_ : Measured v a}}
    -> (v -> Bool)
    -> v
    -> (t : FingerTree v a) {{_ : IsNonempty t}}
    -> Split (FingerTree v a) a
  splitTree _ _ (Single x) = Split: Empty x Empty
  splitTree p i (Deep _ pr m sf) =
    let
      vpr = i <> measure pr
      vm = vpr <> measure m
    in
      if p vpr then (case splitDigit p i pr of \ where
        (Split: l x r) -> Split: (maybe Empty digitToTree l) x (deepL r m sf))
      else if p vm then (case splitTree p vpr m {{believeMe}} of \ where
        (Split: ml xs mr) -> case splitNode p (vpr <> measure ml) xs of \ where
          (Split: l x r) -> Split: (deepR pr ml l) x (deepL r mr sf))
      else (case splitDigit p vm sf of \ where
        (Split: l x r) -> Split: (deepR pr  m  l) x (maybe Empty digitToTree r))

split : {{_ : Measured v a}}
  -> (v -> Bool)
  -> FingerTree v a
  -> FingerTree v a * FingerTree v a
split _ Empty  =  (Empty , Empty)
split p xs with splitTree p mempty xs {{believeMe}}
... | Split: l x r = if p (measure xs) then (l , x <| r) else (xs , Empty)

-------------------------------------------------------------------------------
-- search
-------------------------------------------------------------------------------

data SearchResult (v a : Set) : Set where
  Position : FingerTree v a -> a -> FingerTree v a -> SearchResult v a
  OnLeft : SearchResult v a
  OnRight : SearchResult v a
  Nowhere : SearchResult v a

private
  searchDigit : {{_ : Measured v a}}
    -> (v -> v -> Bool)
    -> v
    -> Digit a
    -> v
    -> Split (Maybe (Digit a)) a
  searchDigit _ vl (One a) vr = Split: Nothing a Nothing
  searchDigit p vl (Two a b) vr =
    let
      va = vl <> measure a
      vb = measure b <> vr
    in
      if p va vb then Split: Nothing a (Just (One b))
      else Split: (Just (One a)) b Nothing
  searchDigit p vl (Three a b c) vr =
    let
      va = vl <> measure a
      vab = va <> measure b
      vc = measure c <> vr
      vbc = measure b <> vc
    in
      if p va vbc then Split: Nothing a (Just (Two b c))
      else if p vab vc then Split: (Just (One a)) b (Just (One c))
      else Split: (Just (Two a b)) c Nothing
  searchDigit p vl (Four a b c d) vr =
    let
      va = vl <> measure a
      vd = measure d <> vr
      vab = va <> measure b
      vcd = measure c <> vd
      vabc = vab <> measure c
      vbcd = measure b <> vcd
    in
      if p va vbcd then Split: Nothing a (Just (Three b c d))
      else if p vab vcd then Split: (Just (One a)) b (Just (Two c d))
      else if p vabc vd then Split: (Just (Two a b)) c (Just (One d))
      else Split: (Just (Three a b c)) d Nothing

  searchNode : {{_ : Measured v a}}
    -> (v -> v -> Bool)
    -> v
    -> Node v a
    -> v
    -> Split (Maybe (Digit a)) a
  searchNode p vl (Node2 _ a b) vr =
    let
      va = vl <> measure a
      vb = measure b <> vr
    in
      if p va vb then Split: Nothing a (Just (One b))
      else Split: (Just (One a)) b Nothing
  searchNode p vl (Node3 _ a b c) vr =
    let
      va = vl <> measure a
      vab = va <> measure b
      vc = measure c <> vr
      vbc = measure b <> vc
    in
      if p va vbc then Split: Nothing a (Just (Two b c))
      else if p vab vc then Split: (Just (One a)) b (Just (One c))
      else Split: (Just (Two a b)) c Nothing

  searchTree : {{_ : Measured v a}}
    -> (v -> v -> Bool)
    -> v
    -> (t : FingerTree v a) {{_ : IsNonempty t}}
    -> v
    -> Split (FingerTree v a) a
  searchTree _ _ (Single x) _ = Split: Empty x Empty
  searchTree p vl (Deep _ pr m sf) vr =
    let
      vm =  measure m
      vlp =  vl <> measure pr
      vsr =  measure sf <> vr
      vlpm =  vlp <> vm
      vmsr =  vm <> vsr
    in
      if p vlp vmsr then (case searchDigit p vl pr vmsr of \ where
        (Split: l x r) -> Split: (maybe Empty digitToTree l) x (deepL r m sf))
      else if p vlpm vsr then (case searchTree p vlp m {{believeMe}} vsr of \ where
        (Split: ml xs mr) -> case searchNode p (vlp <> measure ml) xs (measure mr <> vsr) of \ where
          (Split: l x r) -> Split: (deepR pr  ml l) x (deepL r mr sf))
      else (case searchDigit p vlpm sf vr of \ where
        (Split: l x r) ->  Split: (deepR pr  m  l) x (maybe Empty digitToTree r))

search : {{_ : Measured v a}}
  -> (v -> v -> Bool)
  -> FingerTree v a
  -> SearchResult v a
search p t =
  let
    vt = measure t
    pleft = p mempty vt
    pright = p vt mempty
  in
    if pleft && pright then OnLeft
    else if not pleft && pright then
      (case searchTree p mempty t {{believeMe}} mempty of \ where
        (Split: l x r) -> Position l x r)
    else if not pleft && not pright then OnRight
    else Nowhere
