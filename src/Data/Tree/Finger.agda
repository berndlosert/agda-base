{-# OPTIONS --type-in-type #-}

module Data.Tree.Finger where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

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
  Measured-FingerTree : {{Measured v a}} -> Measured v (FingerTree v a)
  Measured-FingerTree .measure = \ where
    Empty -> neutral
    (Single x) -> measure x
    (Deep v _ _ _) -> v

  Foldable-FingerTree : Foldable (FingerTree v)
  Foldable-FingerTree .foldr _ z Empty = z
  Foldable-FingerTree .foldr f z (Single x) = f x z
  Foldable-FingerTree .foldr f z (Deep _ pr m sf) =
    foldr f (foldr (flip (foldr f)) (foldr f z sf) m) pr

  Functor-FingerTree : Functor (FingerTree v)
  Functor-FingerTree .map f = \ where
    Empty -> Empty
    (Single x) -> Single (f x)
    (Deep v pr m sf) -> Deep v (map f pr) (map (map f) m) (map f sf)

  Traversable-FingerTree : Traversable (FingerTree v)
  Traversable-FingerTree .traverse f = \ where
    Empty -> pure Empty
    (Single x) -> (| Single (f x) |)
    (Deep v pr m sf) ->
      (| (Deep v) (traverse f pr) (traverse (traverse f) m) (traverse f sf) |)

  Validation-NonEmpty-FingerTree : Validation NonEmpty (FingerTree v a)
  Validation-NonEmpty-FingerTree .validate _ Empty = False
  Validation-NonEmpty-FingerTree .validate _ _ = True

empty : FingerTree v a
empty = Empty

singleton : a -> FingerTree v a
singleton = Single

deep : {{Measured v a}}
  -> Digit a
  -> FingerTree v (Node v a)
  -> Digit a
  -> FingerTree v a
deep pr m sf = Deep (measure pr <> measure m <> measure sf) pr m sf

digitToTree : {{Measured v a}} -> Digit a -> FingerTree v a
digitToTree (One a) = Single a
digitToTree (Two a b) = deep (One a) Empty (One b)
digitToTree (Three a b c) = deep (Two a b) Empty (One c)
digitToTree (Four a b c d) = deep (Two a b) Empty (Two c d)

-------------------------------------------------------------------------------
-- Cons operator
-------------------------------------------------------------------------------

cons : {{Measured v a}} -> a -> FingerTree v a -> FingerTree v a

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

consAll : {{Measured v a}} -> {{Foldable f}}
  -> f a -> FingerTree v a -> FingerTree v a
consAll = flip (foldr cons)

-------------------------------------------------------------------------------
-- Snoc operator
-------------------------------------------------------------------------------

snoc : {{Measured v a}} -> FingerTree v a -> a -> FingerTree v a

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
  app3 Empty ts xs = consAll ts xs
  app3 xs ts Empty = snocAll xs ts
  app3 (Single x) ts xs = cons x (consAll ts xs)
  app3 xs ts (Single x) = snoc (snocAll xs ts) x
  app3 (Deep _ pr1 m1 sf1) ts (Deep _ pr2 m2 sf2) =
    deep pr1 (app3 m1 (nodes (toList sf1 <> ts <> toList pr2)) m2) sf2

instance
  Semigroup-FingerTree : {{Measured v a}} -> Semigroup (FingerTree v a)
  Semigroup-FingerTree ._<>_ xs ys = app3 xs [] ys

  Monoid-FingerTree : {{Measured v a}} -> Monoid (FingerTree v a)
  Monoid-FingerTree .neutral = Empty

-------------------------------------------------------------------------------
-- uncons & unsnoc
-------------------------------------------------------------------------------

uncons : {{Measured v a}}
  -> FingerTree v a
  -> Maybe (Pair a (FingerTree v a))

unsnoc : {{Measured v a}}
  -> FingerTree v a
  -> Maybe (Pair (FingerTree v a) a)

private
  rotL : {{Measured v a}}
    -> FingerTree v (Node v a)
    -> Digit a
    -> FingerTree v a

  rotR : {{Measured v a}}
    -> Digit a
    -> FingerTree v (Node v a)
    -> FingerTree v a

uncons Empty = Nothing
uncons (Single x) = Just (x , Empty)
uncons (Deep _ (One x) m sf) = Just (x , rotL m sf)
uncons (Deep _ (Two a b) m sf) = Just (a , deep (One b) m sf)
uncons (Deep _ (Three a b c) m sf) = Just (a , deep (Two b c) m sf)
uncons (Deep _ (Four a b c d) m sf) = Just (a , deep (Three b c d) m sf)

unsnoc Empty = Nothing
unsnoc (Single x) = Just (Empty , x)
unsnoc (Deep _ pr m (One x)) = Just (rotR pr m , x)
unsnoc (Deep _ pr m (Two a b)) = Just (deep pr m (One a) , b)
unsnoc (Deep _ pr m (Three a b c)) = Just (deep pr m (Two a b) , c)
unsnoc (Deep _ pr m (Four a b c d)) = Just (deep pr m (Three a b c) , d)

rotL m sf =
  case uncons m of \ where
    Nothing -> digitToTree sf
    (Just (a , m')) -> Deep (measure m <> measure sf) (nodeToDigit a) m' sf

rotR pr m =
  case unsnoc m of \ where
    Nothing -> digitToTree pr
    (Just (m' , a)) -> Deep (measure pr <> measure m) pr m' (nodeToDigit a)

-------------------------------------------------------------------------------
-- Splitting
-------------------------------------------------------------------------------

deepL : {{Measured v a}}
  -> Maybe (Digit a)
  -> FingerTree v (Node v a)
  -> Digit a
  -> FingerTree v a
deepL Nothing m sf = rotL m sf
deepL (Just pr) m sf = deep pr m sf

deepR : {{Measured v a}}
  -> Digit a
  -> FingerTree v (Node v a)
  -> Maybe (Digit a)
  -> FingerTree v a
deepR pr m Nothing = rotR pr m
deepR pr m (Just sf) = deep pr m sf

splitTree : {{Measured v a}}
  -> (v -> Bool)
  -> v
  -> (t : FingerTree v a)
  -> {{Validate NonEmpty t}}
  -> Split (FingerTree v) a
splitTree _ _ (Single x) = Split: Empty x Empty
splitTree p i (Deep _ pr m sf) =
  let
    vpr = i <> measure pr
    vm = vpr <> measure m
  in
    if p vpr then (case splitDigit p i pr of \ where
      (Split: l x r) -> Split: (maybe Empty digitToTree l) x (deepL r m sf))
    else if p vm then (case splitTree p vpr m {{trustMe}} of \ where
      (Split: ml xs mr) -> case splitNode p (vpr <> measure ml) xs of \ where
        (Split: l x r) -> Split: (deepR pr ml l) x (deepL r mr sf))
    else (case splitDigit p vm sf of \ where
      (Split: l x r) -> Split: (deepR pr  m  l) x (maybe Empty digitToTree r))

split : {{Measured v a}}
  -> (v -> Bool)
  -> FingerTree v a
  -> Pair (FingerTree v a) (FingerTree v a)
split _ Empty  =  (Empty , Empty)
split p xs =
  case splitTree p neutral xs {{trustMe}} of \ where
    (Split: l x r) -> if p (measure xs) then (l , cons x r) else (xs , Empty)

-------------------------------------------------------------------------------
-- Searching
-------------------------------------------------------------------------------

data SearchResult (v a : Set) : Set where
  Position : FingerTree v a -> a -> FingerTree v a -> SearchResult v a
  OnLeft : SearchResult v a
  OnRight : SearchResult v a
  Nowhere : SearchResult v a

private
  searchTree : {{Measured v a}}
    -> (v -> v -> Bool)
    -> v
    -> (t : FingerTree v a)
    -> {{Validate NonEmpty t}}
    -> v
    -> Split (FingerTree v) a
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
      else if p vlpm vsr then (case searchTree p vlp m {{trustMe}} vsr of \ where
        (Split: ml xs mr) -> case searchNode p (vlp <> measure ml) xs (measure mr <> vsr) of \ where
          (Split: l x r) -> Split: (deepR pr  ml l) x (deepL r mr sf))
      else (case searchDigit p vlpm sf vr of \ where
        (Split: l x r) -> Split: (deepR pr m l) x (maybe Empty digitToTree r))

search : {{Measured v a}}
  -> (v -> v -> Bool)
  -> FingerTree v a
  -> SearchResult v a
search p t =
  let
    vt = measure t
    pleft = p neutral vt
    pright = p vt neutral
  in
    if pleft && pright then OnLeft
    else if not pleft && pright then
      (case searchTree p neutral t {{trustMe}} neutral of \ where
        (Split: l x r) -> Position l x r)
    else if not pleft && not pright then OnRight
    else Nowhere

-------------------------------------------------------------------------------
-- Misc.
-------------------------------------------------------------------------------

inits : {{Measured v a}}
  -> (FingerTree v a -> b) -> FingerTree v a -> FingerTree v b
inits _ Empty = Empty
inits f (Single x) = Single (f (Single x))
inits f (Deep n pr m sf) =
  let
    f' ms = case unsnoc ms of \ where
      Nothing -> undefined -- Oops!
      (Just (m' , node)) -> map (\ sf' -> f (deep pr m' sf')) (initsNode node)
  in
    Deep n (map (f <<< digitToTree) (initsDigit pr))
      (inits f' m)
      (map (f <<< deep pr m) (initsDigit sf))

tails : {{Measured v a}}
  -> (FingerTree v a -> b) -> FingerTree v a -> FingerTree v b
tails _ Empty = Empty
tails f (Single x) = Single (f (Single x))
tails f (Deep n pr m sf) =
  let
    f' ms = case uncons ms of \ where
      Nothing -> undefined -- Oops!
      (Just (node , m')) -> map (\ pr' -> f (deep pr' m' sf)) (tailsNode node)
  in
    Deep n (map (\ pr' -> f (deep pr' m sf)) (tailsDigit pr))
      (tails f' m)
      (map (f <<< digitToTree) (tailsDigit sf))
