{-# OPTIONS --type-in-type #-}

module Data.Tree.Finger where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Constraint.NonEmpty
open import Data.Foldable
open import Data.Traversable
open import Data.Tree.Finger.Digit
open import Data.Tree.Finger.Measured
open import Data.Tree.Finger.Node
open import Data.Tree.Finger.Split

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b s v : Set
    f : Set -> Set

-------------------------------------------------------------------------------
-- FingerTree
-------------------------------------------------------------------------------

data FingerTree (v a : Set) : Set where
  nil : FingerTree v a
  single : a -> FingerTree v a
  deep : v -> Digit a -> FingerTree v (Node v a) -> Digit a -> FingerTree v a

instance
  Measured-FingerTree : {{Measured v a}} -> Measured v (FingerTree v a)
  Measured-FingerTree .measure = \ where
    nil -> mempty
    (single x) -> measure x
    (deep v _ _ _) -> v

  NonEmptyness-FingerTree : NonEmptyness (FingerTree v a)
  NonEmptyness-FingerTree .nonempty nil = false
  NonEmptyness-FingerTree .nonempty _ = true

  Foldable-FingerTree : Foldable (FingerTree v)
  Foldable-FingerTree .foldr _ z nil = z
  Foldable-FingerTree .foldr f z (single x) = f x z
  Foldable-FingerTree .foldr f z (deep _ pr m sf) =
    foldr f (foldr (flip (foldr f)) (foldr f z sf) m) pr

  Functor-FingerTree : Functor (FingerTree v)
  Functor-FingerTree .map f = \ where
    nil -> nil
    (single x) -> single (f x)
    (deep v pr m sf) -> deep v (map f pr) (map (map f) m) (map f sf)

  Traversable-FingerTree : Traversable (FingerTree v)
  Traversable-FingerTree .traverse f = \ where
    nil -> pure nil
    (single x) -> (| single (f x) |)
    (deep v pr m sf) ->
      (| (deep v) (traverse f pr) (traverse (traverse f) m) (traverse f sf) |)

empty : FingerTree v a
empty = nil

singleton : a -> FingerTree v a
singleton = single

deep' : {{Measured v a}}
  -> Digit a
  -> FingerTree v (Node v a)
  -> Digit a
  -> FingerTree v a
deep' pr m sf = deep (measure pr <> measure m <> measure sf) pr m sf

digitToTree : {{Measured v a}} -> Digit a -> FingerTree v a
digitToTree (one a) = single a
digitToTree (two a b) = deep' (one a) nil (one b)
digitToTree (three a b c) = deep' (two a b) nil (one c)
digitToTree (four a b c d) = deep' (two a b) nil (two c d)

-------------------------------------------------------------------------------
-- Cons operator
-------------------------------------------------------------------------------

cons : {{Measured v a}} -> a -> FingerTree v a -> FingerTree v a

cons a nil = single a
cons a (single b) = deep' (one a) nil (one b)
cons a (deep s (one b) m sf) =
  deep (measure a <> s) (two a b) m sf
cons a (deep s (two b c) m sf) =
  deep (measure a <> s) (three a b c) m sf
cons a (deep s (three b c d) m sf) =
  deep (measure a <> s) (four a b c d) m sf
cons a (deep s (four b c d e) m sf) =
  deep (measure a <> s) (two a b) (cons (node3' c d e) m) sf

consAll : {{Measured v a}} -> {{Foldable f}}
  -> f a -> FingerTree v a -> FingerTree v a
consAll = flip (foldr cons)

-------------------------------------------------------------------------------
-- Snoc operator
-------------------------------------------------------------------------------

snoc : {{Measured v a}} -> FingerTree v a -> a -> FingerTree v a

snoc nil a = single a
snoc (single a) b = deep' (one a) nil (one b)
snoc (deep s pr m (one a)) b =
  deep (s <> measure b) pr m (two a b)
snoc (deep s pr m (two a b)) c =
  deep (s <> measure c) pr m (three a b c)
snoc (deep s pr m (three a b c)) d =
  deep (s <> measure d) pr m (four a b c d)
snoc (deep s pr m (four a b c d)) e =
  deep (s <> measure e) pr (snoc m (node3' a b c)) (two d e)

snocAll : {{Measured v a}} -> {{Foldable f}}
  -> FingerTree v a -> f a -> FingerTree v a
snocAll = foldl snoc

-------------------------------------------------------------------------------
-- Semigroup & Monoid instances
-------------------------------------------------------------------------------

private
  app3 : {{Measured v a}}
    -> FingerTree v a
    -> List a
    -> FingerTree v a
    -> FingerTree v a
  app3 nil ts xs = consAll ts xs
  app3 xs ts nil = snocAll xs ts
  app3 (single x) ts xs = cons x (consAll ts xs)
  app3 xs ts (single x) = snoc (snocAll xs ts) x
  app3 (deep _ pr1 m1 sf1) ts (deep _ pr2 m2 sf2) =
    deep' pr1 (app3 m1 (nodes (toList sf1 <> ts <> toList pr2)) m2) sf2

instance
  Semigroup-FingerTree : {{Measured v a}} -> Semigroup (FingerTree v a)
  Semigroup-FingerTree ._<>_ xs ys = app3 xs [] ys

  Monoid-FingerTree : {{Measured v a}} -> Monoid (FingerTree v a)
  Monoid-FingerTree .mempty = nil

-------------------------------------------------------------------------------
-- uncons & unsnoc
-------------------------------------------------------------------------------

uncons : {{Measured v a}}
  -> (t : FingerTree v a)
  -> {{Assert $ nonempty t}}
  -> Pair a (FingerTree v a)

unsnoc : {{Measured v a}}
  -> (t : FingerTree v a)
  -> {{Assert $ nonempty t}}
  -> Pair (FingerTree v a) a

private
  rotL : {{Measured v a}}
    -> FingerTree v (Node v a)
    -> Digit a
    -> FingerTree v a

  rotR : {{Measured v a}}
    -> Digit a
    -> FingerTree v (Node v a)
    -> FingerTree v a

uncons nil = error "Data.Tree.Finger.uncons: bad argument"
uncons (single x) = (x , nil)
uncons (deep _ (one x) m sf) = (x , rotL m sf)
uncons (deep _ (two a b) m sf) = (a , deep' (one b) m sf)
uncons (deep _ (three a b c) m sf) = (a , deep' (two b c) m sf)
uncons (deep _ (four a b c d) m sf) = (a , deep' (three b c d) m sf)

unsnoc nil = error "Data.Tree.Finger.unsnoc: bad argument"
unsnoc (single x) = (nil , x)
unsnoc (deep _ pr m (one x)) = (rotR pr m , x)
unsnoc (deep _ pr m (two a b)) = (deep' pr m (one a) , b)
unsnoc (deep _ pr m (three a b c)) = (deep' pr m (two a b) , c)
unsnoc (deep _ pr m (four a b c d)) = (deep' pr m (three a b c) , d)

rotL nil sf = digitToTree sf
rotL m sf = let (a , m') = uncons m {{trustMe}} in
  deep (measure m <> measure sf) (nodeToDigit a) m' sf

rotR pr nil = digitToTree pr
rotR pr m = let (m' , a) = unsnoc m {{trustMe}} in
  deep (measure pr <> measure m) pr m' (nodeToDigit a)

-------------------------------------------------------------------------------
-- Splitting
-------------------------------------------------------------------------------

deep'L : {{Measured v a}}
  -> Maybe (Digit a)
  -> FingerTree v (Node v a)
  -> Digit a
  -> FingerTree v a
deep'L nothing m sf = rotL m sf
deep'L (just pr) m sf = deep' pr m sf

deep'R : {{Measured v a}}
  -> Digit a
  -> FingerTree v (Node v a)
  -> Maybe (Digit a)
  -> FingerTree v a
deep'R pr m nothing = rotR pr m
deep'R pr m (just sf) = deep' pr m sf

splitTree : {{Measured v a}}
  -> (v -> Bool)
  -> v
  -> (t : FingerTree v a)
  -> {{Assert $ nonempty t}}
  -> Split (FingerTree v) a
splitTree _ _ (single x) = toSplit nil x nil
splitTree p i (deep _ pr m sf) =
  let
    vpr = i <> measure pr
    vm = vpr <> measure m
  in
    if p vpr then (case splitDigit p i pr of \ where
      (toSplit l x r) -> toSplit (maybe nil digitToTree l) x (deep'L r m sf))
    else if p vm then (case splitTree p vpr m {{trustMe}} of \ where
      (toSplit ml xs mr) -> case splitNode p (vpr <> measure ml) xs of \ where
        (toSplit l x r) -> toSplit (deep'R pr ml l) x (deep'L r mr sf))
    else (case splitDigit p vm sf of \ where
      (toSplit l x r) -> toSplit (deep'R pr  m  l) x (maybe nil digitToTree r))
splitTree _ _ _ = error "Data.Tree.Fingered.splitTree: bad argument"

split : {{Measured v a}}
  -> (v -> Bool)
  -> FingerTree v a
  -> Pair (FingerTree v a) (FingerTree v a)
split _ nil  =  (nil , nil)
split p xs =
  case splitTree p mempty xs {{trustMe}} of \ where
    (toSplit l x r) -> if p (measure xs) then (l , cons x r) else (xs , nil)

-------------------------------------------------------------------------------
-- Searching
-------------------------------------------------------------------------------

data SearchResult (v a : Set) : Set where
  position : FingerTree v a -> a -> FingerTree v a -> SearchResult v a
  OnLeft : SearchResult v a
  OnRight : SearchResult v a
  Nowhere : SearchResult v a

private
  searchTree : {{Measured v a}}
    -> (v -> v -> Bool)
    -> v
    -> (t : FingerTree v a)
    -> {{Assert $ nonempty t}}
    -> v
    -> Split (FingerTree v) a
  searchTree _ _ (single x) _ = toSplit nil x nil
  searchTree p vl (deep _ pr m sf) vr =
    let
      vm =  measure m
      vlp =  vl <> measure pr
      vsr =  measure sf <> vr
      vlpm =  vlp <> vm
      vmsr =  vm <> vsr
    in
      if p vlp vmsr then (case searchDigit p vl pr vmsr of \ where
        (toSplit l x r) -> toSplit (maybe nil digitToTree l) x (deep'L r m sf))
      else if p vlpm vsr then (case searchTree p vlp m {{trustMe}} vsr of \ where
        (toSplit ml xs mr) -> case searchNode p (vlp <> measure ml) xs (measure mr <> vsr) of \ where
          (toSplit l x r) -> toSplit (deep'R pr  ml l) x (deep'L r mr sf))
      else (case searchDigit p vlpm sf vr of \ where
        (toSplit l x r) -> toSplit (deep'R pr m l) x (maybe nil digitToTree r))
  searchTree _ _ _ _ = error "Data.Tree.Finger.searchTree: bad argument"

search : {{Measured v a}}
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
      (case searchTree p mempty t {{trustMe}} mempty of \ where
        (toSplit l x r) -> position l x r)
    else if not pleft && not pright then OnRight
    else Nowhere

-------------------------------------------------------------------------------
-- Misc.
-------------------------------------------------------------------------------

inits : {{Measured v a}}
  -> (FingerTree v a -> b) -> FingerTree v a -> FingerTree v b
inits _ nil = nil
inits f (single x) = single (f (single x))
inits f (deep n pr m sf) =
  let
    f' ms = case unsnoc ms {{trustMe}} of \ where
      (m' , node) -> map (\ sf' -> f (deep' pr m' sf')) (initsNode node)
  in
    deep n (map (f <<< digitToTree) (initsDigit pr))
      (inits f' m)
      (map (f <<< deep' pr m) (initsDigit sf))

tails : {{Measured v a}}
  -> (FingerTree v a -> b) -> FingerTree v a -> FingerTree v b
tails _ nil = nil
tails f (single x) = single (f (single x))
tails f (deep n pr m sf) =
  let
    f' ms = case uncons ms {{trustMe}} of \ where
      (node , m') -> map (\ pr' -> f (deep' pr' m' sf)) (tailsNode node)
  in
    deep n (map (\ pr' -> f (deep' pr' m sf)) (tailsDigit pr))
      (tails f' m)
      (map (f <<< digitToTree) (tailsDigit sf))

splitMapTreeN : {{Measured Nat a}}
  -> (Nat -> s -> Pair s s)
  -> (s -> Node Nat a -> b)
  -> s -> FingerTree Nat (Node Nat a) -> FingerTree Nat b
splitMapTreeN split f s nil = nil
splitMapTreeN split f s (single xs) = single (f s xs)
splitMapTreeN split f s (deep n pr m sf) =
  let
    (prs , r) = split (measure pr) s
    (ms , sfs) = split (measure m) r
    pr' = splitMapDigit split f prs pr
    m' = splitMapTreeN split (splitMapNode split f) ms m
    sf' = splitMapDigit split f sfs sf
  in
    deep n pr' m' sf'

splitMapTreeE : {{Measured Nat a}}
  -> (Nat -> s -> Pair s s)
  -> (s -> a -> b)
  -> s -> FingerTree Nat a -> FingerTree Nat b
splitMapTreeE split f s nil = nil
splitMapTreeE split f s (single xs) = single (f s xs)
splitMapTreeE split f s (deep n pr m sf) =
  let
    spr = measure pr
    sm = n - spr - measure sf
    (prs , r) = split spr s
    (ms , sfs) = split sm r
    pr' = splitMapDigit split f prs pr
    m' = splitMapTreeN split (splitMapNode split f) ms m
    sf' = splitMapDigit split f sfs sf
  in
    deep n pr' m' sf'
