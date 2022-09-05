module Data.Tree.Finger where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Data.Foldable
open import Data.Monoid.Sum
open import Data.NonEmpty
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
  empty : FingerTree v a
  singleton : a -> FingerTree v a
  deep : v -> Digit a -> FingerTree v (Node v a) -> Digit a -> FingerTree v a

instance
  Measured-FingerTree : {{Measured v a}} -> Measured v (FingerTree v a)
  Measured-FingerTree .measure = \ where
    empty -> mempty
    (singleton x) -> measure x
    (deep v _ _ _) -> v

  HasNonEmpty-FingerTree : HasNonEmpty (FingerTree v a)
  HasNonEmpty-FingerTree .isNonEmpty empty = false
  HasNonEmpty-FingerTree .isNonEmpty _ = true

  Foldable-FingerTree : Foldable (FingerTree v)
  Foldable-FingerTree .foldr _ init empty = init
  Foldable-FingerTree .foldr step init (singleton x) = step x init
  Foldable-FingerTree .foldr step init (deep _ pr m sf) =
    foldr step (foldr (flip (foldr step)) (foldr step init sf) m) pr

  Functor-FingerTree : Functor (FingerTree v)
  Functor-FingerTree .map f = \ where
    empty -> empty
    (singleton x) -> singleton (f x)
    (deep v pr m sf) -> deep v (map f pr) (map (map f) m) (map f sf)

  Traversable-FingerTree : Traversable (FingerTree v)
  Traversable-FingerTree .traverse f = \ where
    empty -> pure empty
    (singleton x) -> (| singleton (f x) |)
    (deep v pr m sf) ->
      (| (deep v) (traverse f pr) (traverse (traverse f) m) (traverse f sf) |)

mkDeep : {{Measured v a}}
  -> Digit a
  -> FingerTree v (Node v a)
  -> Digit a
  -> FingerTree v a
mkDeep pr m sf = deep (measure pr <> measure m <> measure sf) pr m sf

digitToTree : {{Measured v a}} -> Digit a -> FingerTree v a
digitToTree (one a) = singleton a
digitToTree (two a b) = mkDeep (one a) empty (one b)
digitToTree (three a b c) = mkDeep (two a b) empty (one c)
digitToTree (four a b c d) = mkDeep (two a b) empty (two c d)

-------------------------------------------------------------------------------
-- Cons operator
-------------------------------------------------------------------------------

cons : {{Measured v a}} -> a -> FingerTree v a -> FingerTree v a

cons a empty = singleton a
cons a (singleton b) = mkDeep (one a) empty (one b)
cons a (deep s (one b) m sf) =
  deep (measure a <> s) (two a b) m sf
cons a (deep s (two b c) m sf) =
  deep (measure a <> s) (three a b c) m sf
cons a (deep s (three b c d) m sf) =
  deep (measure a <> s) (four a b c d) m sf
cons a (deep s (four b c d e) m sf) =
  deep (measure a <> s) (two a b) (cons (mkNode3 c d e) m) sf

consAll : {{Measured v a}} -> {{Foldable f}}
  -> f a -> FingerTree v a -> FingerTree v a
consAll = flip (foldr cons)

-------------------------------------------------------------------------------
-- Snoc operator
-------------------------------------------------------------------------------

snoc : {{Measured v a}} -> FingerTree v a -> a -> FingerTree v a

snoc empty a = singleton a
snoc (singleton a) b = mkDeep (one a) empty (one b)
snoc (deep s pr m (one a)) b =
  deep (s <> measure b) pr m (two a b)
snoc (deep s pr m (two a b)) c =
  deep (s <> measure c) pr m (three a b c)
snoc (deep s pr m (three a b c)) d =
  deep (s <> measure d) pr m (four a b c d)
snoc (deep s pr m (four a b c d)) e =
  deep (s <> measure e) pr (snoc m (mkNode3 a b c)) (two d e)

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
  app3 empty ts xs = consAll ts xs
  app3 xs ts empty = snocAll xs ts
  app3 (singleton x) ts xs = cons x (consAll ts xs)
  app3 xs ts (singleton x) = snoc (snocAll xs ts) x
  app3 (deep _ pr1 m1 sf1) ts (deep _ pr2 m2 sf2) =
    mkDeep pr1 (app3 m1 (nodes (toList sf1 <> ts <> toList pr2)) m2) sf2

instance
  Semigroup-FingerTree : {{Measured v a}} -> Semigroup (FingerTree v a)
  Semigroup-FingerTree ._<>_ xs ys = app3 xs [] ys

  Monoid-FingerTree : {{Measured v a}} -> Monoid (FingerTree v a)
  Monoid-FingerTree .mempty = empty

-------------------------------------------------------------------------------
-- uncons & unsnoc
-------------------------------------------------------------------------------

uncons : {{Measured v a}}
  -> (FingerTree v a)
  -> Maybe (Pair a (FingerTree v a))

unsnoc : {{Measured v a}}
  -> (FingerTree v a)
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

uncons empty = nothing
uncons (singleton x) = just (x , empty)
uncons (deep _ (one x) m sf) = just (x , rotL m sf)
uncons (deep _ (two a b) m sf) = just (a , mkDeep (one b) m sf)
uncons (deep _ (three a b c) m sf) = just (a , mkDeep (two b c) m sf)
uncons (deep _ (four a b c d) m sf) = just (a , mkDeep (three b c d) m sf)

unsnoc empty = nothing
unsnoc (singleton x) = just (empty , x)
unsnoc (deep _ pr m (one x)) = just (rotR pr m , x)
unsnoc (deep _ pr m (two a b)) = just (mkDeep pr m (one a) , b)
unsnoc (deep _ pr m (three a b c)) = just (mkDeep pr m (two a b) , c)
unsnoc (deep _ pr m (four a b c d)) = just (mkDeep pr m (three a b c) , d)

rotL m sf with uncons m
... | nothing = digitToTree sf 
... | just (a , m')  = deep (measure m <> measure sf) (nodeToDigit a) m' sf 

rotR pr m with unsnoc m
... | nothing = digitToTree pr
... | just (m' , a) = deep (measure pr <> measure m) pr m' (nodeToDigit a)

-------------------------------------------------------------------------------
-- Splitting
-------------------------------------------------------------------------------

mkDeepL : {{Measured v a}}
  -> Maybe (Digit a)
  -> FingerTree v (Node v a)
  -> Digit a
  -> FingerTree v a
mkDeepL nothing m sf = rotL m sf
mkDeepL (just pr) m sf = mkDeep pr m sf

mkDeepR : {{Measured v a}}
  -> Digit a
  -> FingerTree v (Node v a)
  -> Maybe (Digit a)
  -> FingerTree v a
mkDeepR pr m nothing = rotR pr m
mkDeepR pr m (just sf) = mkDeep pr m sf

splitTree : {{Measured v a}}
  -> (v -> Bool)
  -> v
  -> FingerTree v a
  -> Maybe (Split (FingerTree v) a)
splitTree _ _ empty = nothing
splitTree _ _ (singleton x) = just (toSplit empty x empty)
splitTree p i (deep _ pr m sf) =
  let
    vpr = i <> measure pr
    vm = vpr <> measure m
  in
    if p vpr then (case splitDigit p i pr of \ where
      (toSplit l x r) -> just $ toSplit (maybe empty digitToTree l) x (mkDeepL r m sf))
    else if p vm then (case splitTree p vpr m of \ where
      nothing -> nothing
      (just (toSplit ml xs mr)) -> case splitNode p (vpr <> measure ml) xs of \ where
        (toSplit l x r) -> just $ toSplit (mkDeepR pr ml l) x (mkDeepL r mr sf))
    else (case splitDigit p vm sf of \ where
      (toSplit l x r) -> just $ toSplit (mkDeepR pr  m  l) x (maybe empty digitToTree r))

split : {{Measured v a}}
  -> (v -> Bool)
  -> FingerTree v a
  -> Pair (FingerTree v a) (FingerTree v a)
split p xs with splitTree p mempty xs
... | nothing = (empty , empty)
... | just (toSplit l x r) = if p (measure xs) then (l , cons x r) else (xs , empty)

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
    -> FingerTree v a
    -> v
    -> Maybe (Split (FingerTree v) a)
  searchTree _ _ empty _ = nothing 
  searchTree _ _ (singleton x) _ = just (toSplit empty x empty)
  searchTree p vl (deep _ pr m sf) vr =
    let
      vm =  measure m
      vlp =  vl <> measure pr
      vsr =  measure sf <> vr
      vlpm =  vlp <> vm
      vmsr =  vm <> vsr
    in
      if p vlp vmsr then (case searchDigit p vl pr vmsr of \ where
        (toSplit l x r) -> just $ toSplit (maybe empty digitToTree l) x (mkDeepL r m sf))
      else if p vlpm vsr then (case searchTree p vlp m vsr of \ where
        nothing -> nothing
        (just (toSplit ml xs mr)) -> case searchNode p (vlp <> measure ml) xs (measure mr <> vsr) of \ where
          (toSplit l x r) -> just $ toSplit (mkDeepR pr  ml l) x (mkDeepL r mr sf))
      else (case searchDigit p vlpm sf vr of \ where
        (toSplit l x r) -> just $ toSplit (mkDeepR pr m l) x (maybe empty digitToTree r))

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
      (case searchTree p mempty t mempty of \ where
        nothing -> Nowhere
        (just (toSplit l x r)) -> position l x r)
    else if not pleft && not pright then OnRight
    else Nowhere

-------------------------------------------------------------------------------
-- Misc.
-------------------------------------------------------------------------------

inits : {{Measured v a}}
  -> (FingerTree v a -> b) -> FingerTree v a -> FingerTree v b
inits _ empty = empty
inits f (singleton x) = singleton (f (singleton x))
inits f (deep n pr m sf) =
  let
    f' ms = case fromJust (unsnoc ms) of \ where
      (m' , node) -> map (\ sf' -> f (mkDeep pr m' sf')) (initsNode node)
  in
    deep n (map (f <<< digitToTree) (initsDigit pr))
      (inits f' m)
      (map (f <<< mkDeep pr m) (initsDigit sf))

tails : {{Measured v a}}
  -> (FingerTree v a -> b) -> FingerTree v a -> FingerTree v b
tails _ empty = empty
tails f (singleton x) = singleton (f (singleton x))
tails f (deep n pr m sf) =
  let
    f' ms = case fromJust (uncons ms) of \ where
      (node , m') -> map (\ pr' -> f (mkDeep pr' m' sf)) (tailsNode node)
  in
    deep n (map (\ pr' -> f (mkDeep pr' m sf)) (tailsDigit pr))
      (tails f' m)
      (map (f <<< digitToTree) (tailsDigit sf))
