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
    f : Set -> Set

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

empty : FingerTree v a
empty = Empty

singleton : a -> FingerTree v a
singleton = Single

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

cons : {{_ : Measured v a}} -> a -> FingerTree v a -> FingerTree v a

cons a Empty = Single a
cons a (Single b) = deep (One a) Empty (One b)
cons a (Deep s (One b) m sf) =
  Deep (measure a <> s) (Two a b) m sf
cons a (Deep s (Two b c) m sf) =
  Deep (measure a <> s) (Three a b c) m sf
cons a (Deep s (Three b c d) m sf) =
  Deep (measure a <> s) (Four a b c d) m sf
cons a (Deep s (Four b c d e) m sf) =
  Deep (measure a <> s) (Two a b) (cons (node3 c d e) m) sf

consAll : {{_ : Measured v a}} {{_ : Foldable f}}
  -> f a -> FingerTree v a -> FingerTree v a
consAll = flip (foldr cons)

-------------------------------------------------------------------------------
-- Snoc operator
-------------------------------------------------------------------------------

snoc : {{_ : Measured v a}} -> FingerTree v a -> a -> FingerTree v a

snoc Empty a = Single a
snoc (Single a) b = deep (One a) Empty (One b)
snoc (Deep s pr m (One a)) b =
  Deep (s <> measure b) pr m (Two a b)
snoc (Deep s pr m (Two a b)) c =
  Deep (s <> measure c) pr m (Three a b c)
snoc (Deep s pr m (Three a b c)) d =
  Deep (s <> measure d) pr m (Four a b c d)
snoc (Deep s pr m (Four a b c d)) e =
  Deep (s <> measure e) pr (snoc m (node3 a b c)) (Two d e)

snocAll : {{_ : Measured v a}} {{_ : Foldable f}}
  -> FingerTree v a -> f a -> FingerTree v a
snocAll = foldl snoc

-------------------------------------------------------------------------------
-- Semigroup & Monoid instances
-------------------------------------------------------------------------------

private
  app3 : {{_ : Measured v a}}
    -> FingerTree v a
    -> List a
    -> FingerTree v a
    -> FingerTree v a
  app3 Empty ts xs = consAll ts xs
  app3 xs ts Empty = snocAll xs ts
  app3 (Single x) ts xs = cons x (consAll ts xs)
  app3 xs ts (Single x) = snoc (snocAll xs ts) x
  app3 (Deep _ pr1 m1 sf1) ts (Deep _ pr2 m2 sf2) =
    deep pr1 (app3 m1 (nodes (toList sf1 <> ts <> toList pr2)) m2) sf2

instance
  Semigroup-FingerTree : {{_ : Measured v a}} -> Semigroup (FingerTree v a)
  Semigroup-FingerTree ._<>_ xs ys = app3 xs [] ys

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
-- Splitting
-------------------------------------------------------------------------------

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
deepR pr m (Just sf) = deep pr m sf

splitTree : {{_ : Measured v a}}
  -> (v -> Bool)
  -> v
  -> (t : FingerTree v a) {{_ : IsNonempty t}}
  -> FingerTree v a * a * FingerTree v a
splitTree _ _ (Single x) = (Empty , x , Empty)
splitTree p i (Deep _ pr m sf) =
  let
    vpr = i <> measure pr
    vm = vpr <> measure m
  in
    if p vpr then (case splitDigit p i pr of \ where
      (l , x , r) -> (maybe Empty digitToTree l , x , deepL r m sf))
    else if p vm then (case splitTree p vpr m {{believeMe}} of \ where
      (ml , xs , mr) -> case splitNode p (vpr <> measure ml) xs of \ where
        (l , x , r) -> (deepR pr ml l , x , deepL r mr sf))
    else (case splitDigit p vm sf of \ where
      (l , x , r) -> (deepR pr  m  l , x , maybe Empty digitToTree r))

split : {{_ : Measured v a}}
  -> (v -> Bool)
  -> FingerTree v a
  -> FingerTree v a * FingerTree v a
split _ Empty  =  (Empty , Empty)
split p xs with splitTree p mempty xs {{believeMe}}
... | (l , x , r) = if p (measure xs) then (l , cons x r) else (xs , Empty)

-------------------------------------------------------------------------------
-- Searching
-------------------------------------------------------------------------------

data SearchResult (v a : Set) : Set where
  Position : FingerTree v a -> a -> FingerTree v a -> SearchResult v a
  OnLeft : SearchResult v a
  OnRight : SearchResult v a
  Nowhere : SearchResult v a

private
  searchTree : {{_ : Measured v a}}
    -> (v -> v -> Bool)
    -> v
    -> (t : FingerTree v a) {{_ : IsNonempty t}}
    -> v
    -> FingerTree v a * a * FingerTree v a
  searchTree _ _ (Single x) _ = (Empty , x , Empty)
  searchTree p vl (Deep _ pr m sf) vr =
    let
      vm =  measure m
      vlp =  vl <> measure pr
      vsr =  measure sf <> vr
      vlpm =  vlp <> vm
      vmsr =  vm <> vsr
    in
      if p vlp vmsr then (case searchDigit p vl pr vmsr of \ where
        (l , x , r) -> (maybe Empty digitToTree l , x , deepL r m sf))
      else if p vlpm vsr then (case searchTree p vlp m {{believeMe}} vsr of \ where
        (ml , xs , mr) -> case searchNode p (vlp <> measure ml) xs (measure mr <> vsr) of \ where
          (l , x , r) -> (deepR pr  ml l , x , deepL r mr sf))
      else (case searchDigit p vlpm sf vr of \ where
        (l , x , r) ->  (deepR pr m l , x , maybe Empty digitToTree r))

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
        (l , x , r) -> Position l x r)
    else if not pleft && not pright then OnRight
    else Nowhere

-------------------------------------------------------------------------------
-- Misc.
-------------------------------------------------------------------------------

inits : {{_ : Measured v a}}
  -> (FingerTree v a -> b) -> FingerTree v a -> FingerTree v b
inits _ Empty = Empty
inits f (Single x) = Single (f (Single x))
inits f (Deep n pr m sf) =
  let
    f' ms = case viewr ms of \ where
      EmptyR -> undefined -- Oops!
      (m' :> node) -> map (\ sf' -> f (deep pr m' sf')) (initsNode node)
  in
    Deep n (map (f <<< digitToTree) (initsDigit pr))
      (inits f' m)
      (map (f <<< deep pr m) (initsDigit sf))

tails : {{_ : Measured v a}}
  -> (FingerTree v a -> b) -> FingerTree v a -> FingerTree v b
tails _ Empty = Empty
tails f (Single x) = Single (f (Single x))
tails f (Deep n pr m sf) =
  let
    f' ms = case viewl ms of \ where
      EmptyL -> undefined -- Oops!
      (node :< m') -> map (\ pr' -> f (deep pr' m' sf)) (tailsNode node)
  in
    Deep n (map (\ pr' -> f (deep pr' m sf)) (tailsDigit pr))
      (tails f' m)
      (map (f <<< digitToTree) (tailsDigit sf))
