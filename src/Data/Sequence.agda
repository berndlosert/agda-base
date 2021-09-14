{-# OPTIONS --type-in-type #-}

module Data.Sequence where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Constraint.NonEmpty
open import Control.Alternative
open import Data.Foldable
open import Data.Monoid.Endo
open import Data.Monoid.Sum
open import Data.Traversable
open import Data.Tree.Finger as Tree using (FingerTree)
open import Data.Sequence.Elem

-------------------------------------------------------------------------------
-- Re-exports
-------------------------------------------------------------------------------

open Data.Foldable public
open Data.Traversable public

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b c s v : Set
    f t : Set -> Set

-------------------------------------------------------------------------------
-- Seq
-------------------------------------------------------------------------------

private
  data Seq' (a : Set) : Set where
    toSeq : FingerTree (Sum Nat) (Elem a) -> Seq' a

Seq = Seq'

instance
  Semigroup-Seq : Semigroup (Seq a)
  Semigroup-Seq ._<>_ (toSeq l) (toSeq r) = toSeq (l <> r)

  Monoid-Seq : Monoid (Seq a)
  Monoid-Seq .mempty = toSeq Tree.empty

  NonEmptyness-Seq : NonEmptyness (Seq a)
  NonEmptyness-Seq .nonempty (toSeq t) = nonempty t

  Foldable-Seq : Foldable Seq
  Foldable-Seq .foldr f z (toSeq t) = foldr (f <<< getElem) z t

  Functor-Seq : Functor Seq
  Functor-Seq .map f (toSeq t) = toSeq (map (map f) t)

  Applicative-Seq : Applicative Seq
  Applicative-Seq .pure = toSeq <<< Tree.singleton <<< toElem
  Applicative-Seq ._<*>_ fs xs =
      bind fs \ f -> bind xs \ x -> pure (f x)
    where
      bind : Seq a -> (a -> Seq b) -> Seq b
      bind = flip foldMap

  Alternative-Seq : Alternative Seq
  Alternative-Seq .empty = mempty
  Alternative-Seq ._<|>_ = _<>_

  Monad-Seq : Monad Seq
  Monad-Seq ._>>=_ = flip foldMap

  Traversable-Seq : Traversable Seq
  Traversable-Seq .traverse f (toSeq t) = toSeq <$> traverse (traverse f) t

  Eq-Seq : {{Eq a}} -> Eq (Seq a)
  Eq-Seq ._==_ l r = toList l == toList r

-------------------------------------------------------------------------------
-- Private misc.
-------------------------------------------------------------------------------

private
  splitMap : (Sum Nat -> s -> Pair s s)
    -> (s -> a -> b)
    -> s -> Seq a -> Seq b
  splitMap split f0 s0 (toSeq xs0) = toSeq $
    Tree.splitMapTree split (\ where s' (toElem a) -> toElem (f0 s' a)) s0 xs0

-------------------------------------------------------------------------------
-- Construction
-------------------------------------------------------------------------------

pattern nil = toSeq Tree.nil

cons : a -> Seq a -> Seq a
cons x (toSeq xs) = toSeq (Tree.cons (toElem x) xs)

snoc : Seq a -> a -> Seq a
snoc (toSeq xs) x = toSeq (Tree.snoc xs (toElem x))

singleton : a -> Seq a
singleton x = toSeq (Tree.singleton (toElem x))

fromFoldable : {{Foldable t}} -> t a -> Seq a
fromFoldable = foldr cons empty

-------------------------------------------------------------------------------
-- Construction: Repetition
-------------------------------------------------------------------------------

replicate : Nat -> a -> Seq a
replicate 0 _ = nil
replicate (suc n) x = cons x (replicate n x)

replicateA : {{Applicative f}} -> Nat -> f a -> f (Seq a)
replicateA {f} {a} n0 fa = loop n0
  where
    loop : Nat -> f (Seq a)
    loop 0 = pure empty
    loop (suc n) = (| cons fa (loop n) |)

-------------------------------------------------------------------------------
-- Construction: Iterative construction
-------------------------------------------------------------------------------

iterateN : Nat -> (a -> a) -> a -> Seq a
iterateN 0 f x = empty
iterateN 1 f x = singleton x
iterateN (suc n) f x = cons (f x) (iterateN n f x)

-------------------------------------------------------------------------------
-- Destruction
-------------------------------------------------------------------------------

uncons : (xs : Seq a) -> {{Assert $ nonempty xs}} -> Pair a (Seq a)
uncons nil = error "Data.Sequence.uncons: bad argument"
uncons (toSeq t) =
  case Tree.uncons t {{trustMe}} of \ where
    (toElem x , xs) -> (x , toSeq xs)

unsnoc : (xs : Seq a) -> {{Assert $ nonempty xs}} -> Pair (Seq a) a
unsnoc nil = error "Data.Sequence.uncons: bad argument"
unsnoc (toSeq t) =
  case Tree.unsnoc t {{trustMe}} of \ where
    (xs , toElem x) -> (toSeq xs , x)

head : (xs : Seq a) -> {{Assert $ nonempty xs}} -> a
head nil = error "Data.Sequence.head: bad argument"
head xs = fst (uncons xs)

tail : (xs : Seq a) -> {{Assert $ nonempty xs}} -> Seq a
tail nil = error "Data.Sequence.tail: bad argument"
tail xs = snd (uncons xs)

-------------------------------------------------------------------------------
-- Deconstruction: Views
-------------------------------------------------------------------------------

data Uncons (a : Set) : Seq a -> Set where
  [] : Uncons a nil
  _::_ : (x : a) (xs : Seq a) -> Uncons a (cons x xs)

cons-uncons : (xs : Seq a) {{_ : Assert $ nonempty xs}}
  -> let (y , ys) = uncons xs in cons y ys === xs
cons-uncons _ = trustMe

toUncons : (xs : Seq a) -> Uncons a xs
toUncons nil = []
toUncons xs with uncons xs {{trustMe}} | cons-uncons xs {{trustMe}}
... | (y , ys) | refl = y :: ys

data ViewL (a : Set) : Seq a -> Set where
  [] : ViewL a nil
  _::_ : (x : a) {xs : Seq a} -> ViewL a xs -> ViewL a (cons x xs)

{-# TERMINATING #-}
viewl : (xs : Seq a) -> ViewL a xs
viewl nil = []
viewl xs with toUncons xs
... | [] = []
... | y :: ys = y :: viewl ys

-------------------------------------------------------------------------------
-- Scans
-------------------------------------------------------------------------------

scanl : (b -> a -> b) -> b -> Seq a -> Seq b
scanl f b xs = cons b (snd $ mapAccumL (\ x z -> dup (f x z)) b xs)

scanr : (a -> b -> b) -> b -> Seq a -> Seq b
scanr f b xs = snoc (snd $ mapAccumR (\ z x -> dup (f x z)) b xs) b

-------------------------------------------------------------------------------
-- Sublists
-------------------------------------------------------------------------------

tails : Seq a -> Seq (Seq a)
tails (toSeq t) = snoc (toSeq (Tree.tails (toElem <<< toSeq) t))  empty

inits : Seq a -> Seq (Seq a)
inits (toSeq t) = cons empty (toSeq (Tree.inits (toElem <<< toSeq) t))

-------------------------------------------------------------------------------
-- Sorting
-------------------------------------------------------------------------------


-------------------------------------------------------------------------------
-- Indexing
-------------------------------------------------------------------------------

splitAt : Nat -> Seq a -> Pair (Seq a) (Seq a)
splitAt n (toSeq t) = bimap toSeq toSeq $ Tree.split (\ m -> n < getSum m) t

take : Nat -> Seq a -> Seq a
take n = fst <<< splitAt n

drop : Nat -> Seq a -> Seq a
drop n = snd <<< splitAt n

insertAt : Nat -> a -> Seq a -> Seq a
insertAt n x xs =
  let (l , r) = splitAt n xs
  in l <> singleton x <> r

updateAt : Nat -> (a -> Maybe a) -> Seq a -> Seq a
updateAt _ _ nil = nil
updateAt n f xs =
  let
    (l , r) = splitAt n xs
  in
    case nonempty r of \ where
      true ->
        let (x , r') = uncons r {{trustMe}}
        in l <> maybe r' (flip cons r') (f x)
      false ->
        xs

deleteAt : Nat -> Seq a -> Seq a
deleteAt n = updateAt n (const nothing)

-------------------------------------------------------------------------------
-- Folds
-------------------------------------------------------------------------------

ifoldr : (Nat -> a -> b -> b) -> b -> Seq a -> b
ifoldr {a} {b} f z xs =
    foldr go (const z) xs 0
  where
    go : a -> (Nat -> b) -> Nat -> b
    go x g n = f n x (g (n + 1))

ifoldl : (b -> Nat -> a -> b) -> b -> Seq a -> b
ifoldl {b} {a} f z xs =
    foldl go (const z) xs (length xs - 1)
  where
    go : (Nat -> b) -> a -> Nat -> b
    go g x n = f (g (n - 1)) n x

-------------------------------------------------------------------------------
-- Indexing: Indexing with predicates
-------------------------------------------------------------------------------

indicesl : (a -> Bool) -> Seq a -> List Nat
indicesl {a} p = ifoldr go []
  where
    go : Nat -> a -> List Nat -> List Nat
    go n x ns = if p x then n :: ns else ns

indicesr : (a -> Bool) -> Seq a -> List Nat
indicesr {a} p = ifoldl go []
  where
    go : List Nat -> Nat -> a -> List Nat
    go ns n x = if p x then n :: ns else ns

filterA : {{Applicative f}} -> (a -> f Bool) -> Seq a -> f (Seq a)
filterA {f} {a} p = foldr go (pure empty)
  where
    go : a -> f (Seq a) -> f (Seq a)
    go x xs = (| if_then_else_ (p x) (| (cons x) xs |) xs |)

-------------------------------------------------------------------------------
-- Sublists: Sequential searches
-------------------------------------------------------------------------------

breakl : (a -> Bool) -> Seq a -> Pair (Seq a) (Seq a)
breakl p xs = foldr (\ n _ -> splitAt n xs) (xs , empty) (indicesl p xs)

breakr : (a -> Bool) -> Seq a -> Pair (Seq a) (Seq a)
breakr p xs =
  foldr (\ n _ -> swap (splitAt (suc n) xs)) (xs , empty) (indicesr p xs)

spanl : (a -> Bool) -> Seq a -> Pair (Seq a) (Seq a)
spanl p = breakl (not <<< p)

spanr : (a -> Bool) -> Seq a -> Pair (Seq a) (Seq a)
spanr p = breakr (not <<< p)

takeWhileL : (a -> Bool) -> Seq a -> Seq a
takeWhileL p = fst <<< spanl p

takeWhileR : (a -> Bool) -> Seq a -> Seq a
takeWhileR p = fst <<< spanr p

dropWhileL : (a -> Bool) -> Seq a -> Seq a
dropWhileL p = snd <<< spanl p

dropWhileR : (a -> Bool) -> Seq a -> Seq a
dropWhileR p = snd <<< spanr p

partition : (a -> Bool) -> Seq a -> Pair (Seq a) (Seq a)
partition {a} p = foldl go (empty , empty)
  where
    go : Pair (Seq a) (Seq a) -> a -> Pair (Seq a) (Seq a)
    go (xs , ys) x = if p x then (snoc xs x , ys) else (xs , snoc ys x)

filter : (a -> Bool) -> Seq a -> Seq a
filter {a} p = foldl go empty
  where
    go : Seq a -> a -> Seq a
    go xs x = if p x then snoc xs x else xs

-------------------------------------------------------------------------------
-- Transformations
-------------------------------------------------------------------------------

reverse : Seq a -> Seq a
reverse = foldl (flip cons) empty

intersperse : a -> Seq a -> Seq a
intersperse sep nil = nil
intersperse sep xs =
  let (y , ys) = uncons xs {{trustMe}}
  in cons y (| _#_ ys (cons (const sep) (singleton id)) |)

-------------------------------------------------------------------------------
-- Transformations: Zips and unzip
-------------------------------------------------------------------------------

{-# TERMINATING #-}
zipWith : (a -> b -> c) -> Seq a -> Seq b -> Seq c
zipWith f nil _ = nil
zipWith f _ nil = nil
zipWith f as bs =
  let
    (x , xs) = uncons as {{trustMe}}
    (y , ys) = uncons bs {{trustMe}}
  in
    cons (f x y) (zipWith f xs ys)

zip : Seq a -> Seq b -> Seq (Pair a b)
zip = zipWith _,_

-- Zips together a list of heads and a list of tails.
zipCons : Seq a -> Seq (Seq a) -> Seq (Seq a)
zipCons {a} heads tails =
    (zipWith cons heads (tails <> padding)) <> excess
  where
    -- Extra tails that will be zipped with those heads that have no
    -- corresponding tail in tails.
    padding : Seq (Seq a)
    padding = replicate (length heads - length tails) empty
    -- The tails that cannot be zipped because they have no corresponding
    -- head in heads.
    excess : Seq (Seq a)
    excess = snd (splitAt (length heads) tails)
