module Data.Tree.Finger where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Data.Monoid.Foldable
open import Data.Monoid.Sum
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
    a b s v : Type
    f : Type -> Type

-------------------------------------------------------------------------------
-- Tree
-------------------------------------------------------------------------------

data Tree (v a : Type) : Type where
  empty : Tree v a
  singleton : a -> Tree v a
  deep : v -> Digit a -> Tree v (Node v a) -> Digit a -> Tree v a

instance
  Measured-Tree : {{Measured v a}} -> Measured v (Tree v a)
  Measured-Tree .measure = \ where
    empty -> mempty
    (singleton x) -> measure x
    (deep v _ _ _) -> v

  Foldable-Tree : Foldable (Tree v)
  Foldable-Tree .foldMap _ empty = mempty
  Foldable-Tree .foldMap f (singleton x) = f x
  Foldable-Tree .foldMap f (deep _ pr m sf) =
    foldMap f pr <> foldMap (foldMap f) m <> foldMap f sf

  Functor-Tree : Functor (Tree v)
  Functor-Tree .map f = \ where
    empty -> empty
    (singleton x) -> singleton (f x)
    (deep v pr m sf) -> deep v (map f pr) (map (map f) m) (map f sf)

  Traversable-Tree : Traversable (Tree v)
  Traversable-Tree .traverse f = \ where
    empty -> pure empty
    (singleton x) -> (| singleton (f x) |)
    (deep v pr m sf) ->
      (| (deep v) (traverse f pr) (traverse (traverse f) m) (traverse f sf) |)

mkDeep : {{Measured v a}}
  -> Digit a
  -> Tree v (Node v a)
  -> Digit a
  -> Tree v a
mkDeep pr m sf = deep (measure pr <> measure m <> measure sf) pr m sf

digitToTree : {{Measured v a}} -> Digit a -> Tree v a
digitToTree (one a) = singleton a
digitToTree (two a b) = mkDeep (one a) empty (one b)
digitToTree (three a b c) = mkDeep (two a b) empty (one c)
digitToTree (four a b c d) = mkDeep (two a b) empty (two c d)

-------------------------------------------------------------------------------
-- Cons operator
-------------------------------------------------------------------------------

cons : {{Measured v a}} -> a -> Tree v a -> Tree v a

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
  -> f a -> Tree v a -> Tree v a
consAll xs = flip (foldr cons) xs

-------------------------------------------------------------------------------
-- Snoc operator
-------------------------------------------------------------------------------

snoc : {{Measured v a}} -> Tree v a -> a -> Tree v a

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
  -> Tree v a -> f a -> Tree v a
snocAll = foldl snoc

-------------------------------------------------------------------------------
-- Semigroup & Monoid instances
-------------------------------------------------------------------------------

private
  app3 : {{Measured v a}}
    -> Tree v a
    -> List a
    -> Tree v a
    -> Tree v a
  app3 empty ts xs = consAll ts xs
  app3 xs ts empty = snocAll xs ts
  app3 (singleton x) ts xs = cons x (consAll ts xs)
  app3 xs ts (singleton x) = snoc (snocAll xs ts) x
  app3 (deep _ pr1 m1 sf1) ts (deep _ pr2 m2 sf2) =
    mkDeep pr1 (app3 m1 (nodes (toList sf1 <> ts <> toList pr2)) m2) sf2

instance
  Semigroup-Tree : {{Measured v a}} -> Semigroup (Tree v a)
  Semigroup-Tree ._<>_ xs ys = app3 xs [] ys

  Monoid-Tree : {{Measured v a}} -> Monoid (Tree v a)
  Monoid-Tree .mempty = empty

-------------------------------------------------------------------------------
-- uncons & unsnoc
-------------------------------------------------------------------------------

uncons : {{Measured v a}}
  -> (Tree v a)
  -> Maybe (Tuple a (Tree v a))

unsnoc : {{Measured v a}}
  -> (Tree v a)
  -> Maybe (Tuple (Tree v a) a)

private
  rotL : {{Measured v a}}
    -> Tree v (Node v a)
    -> Digit a
    -> Tree v a

  rotR : {{Measured v a}}
    -> Digit a
    -> Tree v (Node v a)
    -> Tree v a

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
... | just (a , n)  = deep (measure m <> measure sf) (nodeToDigit a) n sf

rotR pr m with unsnoc m
... | nothing = digitToTree pr
... | just (n , a) = deep (measure pr <> measure m) pr n (nodeToDigit a)

-------------------------------------------------------------------------------
-- Splitting
-------------------------------------------------------------------------------

mkDeepL : {{Measured v a}}
  -> Maybe (Digit a)
  -> Tree v (Node v a)
  -> Digit a
  -> Tree v a
mkDeepL nothing m sf = rotL m sf
mkDeepL (just pr) m sf = mkDeep pr m sf

mkDeepR : {{Measured v a}}
  -> Digit a
  -> Tree v (Node v a)
  -> Maybe (Digit a)
  -> Tree v a
mkDeepR pr m nothing = rotR pr m
mkDeepR pr m (just sf) = mkDeep pr m sf

splitTree : {{Measured v a}}
  -> (v -> Bool)
  -> v
  -> Tree v a
  -> Maybe (Split (Tree v) a)
splitTree _ _ empty = nothing
splitTree _ _ (singleton x) = just (empty , x , empty)
splitTree p i (deep _ pr m sf) =
  let
    vpr = i <> measure pr
    vm = vpr <> measure m
  in
    if p vpr then (case (splitDigit p i pr) \ where
      (l , x , r) -> just (maybe empty digitToTree l , x , mkDeepL r m sf))
    else if p vm then (case (splitTree p vpr m) \ where
      nothing -> nothing
      (just (ml , xs , mr)) -> case (splitNode p (vpr <> measure ml) xs) \ where
        (l , x , r) -> just (mkDeepR pr ml l , x , mkDeepL r mr sf))
    else (case (splitDigit p vm sf) \ where
      (l , x , r) -> just (mkDeepR pr  m  l , x , maybe empty digitToTree r))

split : {{Measured v a}}
  -> (v -> Bool)
  -> Tree v a
  -> Tuple (Tree v a) (Tree v a)
split p xs with splitTree p mempty xs
... | nothing = (empty , empty)
... | just (l , x , r) = if p (measure xs) then (l , cons x r) else (xs , empty)

-------------------------------------------------------------------------------
-- Searching
-------------------------------------------------------------------------------

data SearchResult (v a : Type) : Type where
  position : Tree v a -> a -> Tree v a -> SearchResult v a
  onLeft : SearchResult v a
  onRight : SearchResult v a
  nowhere : SearchResult v a

private
  searchTree : {{Measured v a}}
    -> (v -> v -> Bool)
    -> v
    -> Tree v a
    -> v
    -> Maybe (Split (Tree v) a)
  searchTree _ _ empty _ = nothing
  searchTree _ _ (singleton x) _ = just (empty , x , empty)
  searchTree p vl (deep _ pr m sf) vr =
    let
      vm =  measure m
      vlp =  vl <> measure pr
      vsr =  measure sf <> vr
      vlpm =  vlp <> vm
      vmsr =  vm <> vsr
    in
      if p vlp vmsr then (case (searchDigit p vl pr vmsr) \ where
        (l , x , r) -> just ((maybe empty digitToTree l , x , mkDeepL r m sf)))
      else if p vlpm vsr then (case (searchTree p vlp m vsr) \ where
        nothing -> nothing
        (just (ml , xs , mr)) -> case (searchNode p (vlp <> measure ml) xs (measure mr <> vsr)) \ where
          (l , x , r) -> just (mkDeepR pr ml l ,  x , mkDeepL r mr sf))
      else (case (searchDigit p vlpm sf vr) \ where
        (l , x , r) -> just (mkDeepR pr m l , x , maybe empty digitToTree r))

search : {{Measured v a}}
  -> (v -> v -> Bool)
  -> Tree v a
  -> SearchResult v a
search p t =
  let
    vt = measure t
    pleft = p mempty vt
    pright = p vt mempty
  in
    if pleft && pright then onLeft
    else if not pleft && pright then
      (case (searchTree p mempty t mempty) \ where
        nothing -> nowhere
        (just (l , x , r)) -> position l x r)
    else if not pleft && not pright then onRight
    else nowhere

-------------------------------------------------------------------------------
-- Misc.
-------------------------------------------------------------------------------

inits : {{Measured v a}}
  -> (Tree v a -> b) -> Tree v a -> Tree v b
inits _ empty = empty
inits f (singleton x) = singleton (f (singleton x))
inits f (deep n pr m sf) =
  let
    g ms = case (fromJust (unsnoc ms) {{trustMe}}) \ where
      (n , node) -> map (\ sg -> f (mkDeep pr n sg)) (initsNode node)
  in
    deep n (map (f <<< digitToTree) (initsDigit pr))
      (inits g m)
      (map (f <<< mkDeep pr m) (initsDigit sf))

tails : {{Measured v a}}
  -> (Tree v a -> b) -> Tree v a -> Tree v b
tails _ empty = empty
tails f (singleton x) = singleton (f (singleton x))
tails f (deep n pr m sf) =
  let
    g ms = case (fromJust (uncons ms) {{trustMe}}) \ where
      (node , n) -> map (\ pr1 -> f (mkDeep pr1 n sf)) (tailsNode node)
  in
    deep n (map (\ pr1 -> f (mkDeep pr1 m sf)) (tailsDigit pr))
      (tails g m)
      (map (f <<< digitToTree) (tailsDigit sf))
