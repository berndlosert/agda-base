module Data.Sequence where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Data.Filterable
open import Data.Monoid.Foldable
open import Data.Monoid.Endo
open import Data.Monoid.Sum
open import Data.Traversable
open import Data.Tree.Finger as Tree using (Tree)
open import Data.Sequence.Elem

-------------------------------------------------------------------------------
-- Re-exports
-------------------------------------------------------------------------------

open Data.Filterable public
open Data.Monoid.Foldable public
open Data.Traversable public

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b c s v : Type
    f t : Type -> Type

-------------------------------------------------------------------------------
-- Seq
-------------------------------------------------------------------------------

private
  record Seq' (a : Type) : Type where
    constructor asSeq
    field unSeq : Tree (Sum Nat) (Elem a)

  open Seq'

Seq = Seq'

-------------------------------------------------------------------------------
-- Constructors
-------------------------------------------------------------------------------

pattern nil = asSeq Tree.empty

cons : a -> Seq a -> Seq a
cons x xs = asSeq (Tree.cons (elem x) (unSeq xs))

snoc : Seq a -> a -> Seq a
snoc xs x = asSeq (Tree.snoc (unSeq xs) (elem x))

singleton : a -> Seq a
singleton x = asSeq (Tree.singleton (elem x))

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

instance
  Semigroup-Seq : Semigroup (Seq a)
  Semigroup-Seq ._<>_ l r = asSeq (unSeq l <> unSeq r)

  Monoid-Seq : Monoid (Seq a)
  Monoid-Seq .mempty = asSeq Tree.empty

  Foldable-Seq : Foldable Seq
  Foldable-Seq .foldMap f xs = foldMap (f <<< getElem) (unSeq xs)

  Functor-Seq : Functor Seq
  Functor-Seq .map f xs = asSeq (map f <$> unSeq xs)

  Applicative-Seq : Applicative Seq
  Applicative-Seq .pure = asSeq <<< Tree.singleton <<< elem
  Applicative-Seq ._<*>_ fs xs =
      bind fs \ f -> bind xs \ x -> pure (f x)
    where
      bind : Seq a -> (a -> Seq b) -> Seq b
      bind = flip foldMap

  Alternative-Seq : Alternative Seq
  Alternative-Seq .azero = mempty
  Alternative-Seq ._<|>_ = _<>_

  Monad-Seq : Monad Seq
  Monad-Seq ._>>=_ = flip foldMap

  Traversable-Seq : Traversable Seq
  Traversable-Seq .traverse f xs = asSeq <$> traverse (traverse f) (unSeq xs)

  Filterable-Seq : Filterable Seq
  Filterable-Seq .mapMaybe f = foldr (go f) nil
    where
      go : (a -> Maybe b) -> a -> Seq b -> Seq b
      go f x ys = case (f x) \ where
        nothing -> ys
        (just y) -> cons y ys

  Eq-Seq : {{Eq a}} -> Eq (Seq a)
  Eq-Seq ._==_ l r = toList l == toList r

-------------------------------------------------------------------------------
-- Constructors: Other
-------------------------------------------------------------------------------

fromFoldable : {{Foldable t}} -> t a -> Seq a
fromFoldable = foldr cons azero

replicate : Nat -> a -> Seq a
replicate 0 _ = nil
replicate (suc n) x = cons x (replicate n x)

replicateA : {{Applicative f}} -> Nat -> f a -> f (Seq a)
replicateA {f} {a} n0 fa = loop n0
  where
    loop : Nat -> f (Seq a)
    loop 0 = pure azero
    loop (suc n) = (| cons fa (loop n) |)

iterateN : Nat -> (a -> a) -> a -> Seq a
iterateN 0 f x = azero
iterateN 1 f x = singleton x
iterateN (suc n) f x = cons (f x) (iterateN n f x)

-------------------------------------------------------------------------------
-- Destructors
-------------------------------------------------------------------------------

uncons : Seq a -> Maybe (Tuple a (Seq a))
uncons xs with Tree.uncons (unSeq xs)
... | nothing = nothing
... | just (elem x , xs) = just (x , asSeq xs)

unsnoc : Seq a -> Maybe (Tuple (Seq a) a)
unsnoc xs with Tree.unsnoc (unSeq xs)
... | nothing = nothing
... | just (xs , elem x) = just (asSeq xs , x)

head : Seq a -> Maybe a
head xs = fst <$> uncons xs

tail : Seq a -> Maybe (Seq a)
tail xs = snd <$> uncons xs

-------------------------------------------------------------------------------
-- Views
-------------------------------------------------------------------------------

data AsList (a : Type) : Seq a -> Type where
  [] : AsList a nil
  _::_ : (x : a) (xs : Seq a) -> AsList a (cons x xs)

prop-uncons : (xs : Seq a) ->
  case (uncons xs) \ where
    nothing -> xs === nil
    (just (y , ys)) -> xs === cons y ys
prop-uncons _ = trustMe

aList : (xs : Seq a) -> AsList a xs
aList xs with uncons xs | prop-uncons xs
... | nothing | refl = []
... | just (y , ys) | refl = y :: ys

data ViewL (a : Type) : Seq a -> Type where
  [] : ViewL a nil
  _::_ : (x : a) {xs : Seq a} -> ViewL a xs -> ViewL a (cons x xs)

viewl : (xs : Seq a) -> ViewL a xs
viewl xs with aList xs
... | [] = []
... | y :: ys = y :: viewl ys

-------------------------------------------------------------------------------
-- Scans
-------------------------------------------------------------------------------

scanl : (b -> a -> b) -> b -> Seq a -> Seq b
scanl f b xs = cons b (snd (mapAccumL (\ x z -> dup (f x z)) b xs))

scanr : (a -> b -> b) -> b -> Seq a -> Seq b
scanr f b xs = snoc (snd (mapAccumR (\ z x -> dup (f x z)) b xs)) b

-------------------------------------------------------------------------------
-- Sublists
-------------------------------------------------------------------------------

tails : Seq a -> Seq (Seq a)
tails xs = snoc (asSeq (Tree.tails (elem <<< asSeq) (unSeq xs))) azero

inits : Seq a -> Seq (Seq a)
inits xs = cons azero (asSeq (Tree.inits (elem <<< asSeq) (unSeq xs)))

-------------------------------------------------------------------------------
-- Indexing
-------------------------------------------------------------------------------

splitAt : Nat -> Seq a -> Tuple (Seq a) (Seq a)
splitAt n xs = case (Tree.split (\ m -> n < getSum m) (unSeq xs)) \ where
  (ys , zs) -> (asSeq ys , asSeq zs)

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
    case (uncons r) \ where
      nothing -> xs
      (just (x , r')) -> l <> maybe r' (flip cons r') (f x)

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

ifoldl' : (b -> Nat -> a -> b) -> b -> Seq a -> b
ifoldl' {b} {a} f z xs =
    foldl' go (const z) xs (length xs - 1)
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
indicesr {a} p = ifoldl' go []
  where
    go : List Nat -> Nat -> a -> List Nat
    go ns n x = if p x then n :: ns else ns

-------------------------------------------------------------------------------
-- Sublists: Sequential searches
-------------------------------------------------------------------------------

breakl : (a -> Bool) -> Seq a -> Tuple (Seq a) (Seq a)
breakl p xs = foldr (\ n _ -> splitAt n xs) (xs , azero) (indicesl p xs)

breakr : (a -> Bool) -> Seq a -> Tuple (Seq a) (Seq a)
breakr p xs =
  foldr (\ n _ -> swap (splitAt (suc n) xs)) (xs , azero) (indicesr p xs)

spanl : (a -> Bool) -> Seq a -> Tuple (Seq a) (Seq a)
spanl p = breakl (not <<< p)

spanr : (a -> Bool) -> Seq a -> Tuple (Seq a) (Seq a)
spanr p = breakr (not <<< p)

takeWhileL : (a -> Bool) -> Seq a -> Seq a
takeWhileL p = fst <<< spanl p

takeWhileR : (a -> Bool) -> Seq a -> Seq a
takeWhileR p = fst <<< spanr p

dropWhileL : (a -> Bool) -> Seq a -> Seq a
dropWhileL p = snd <<< spanl p

dropWhileR : (a -> Bool) -> Seq a -> Seq a
dropWhileR p = snd <<< spanr p

-------------------------------------------------------------------------------
-- Transformations
-------------------------------------------------------------------------------

reverse : Seq a -> Seq a
reverse = foldl' (flip cons) azero

intersperse : a -> Seq a -> Seq a
intersperse sep xs with uncons xs
... | nothing = nil
... | just (y , ys) = cons y (| ys & cons (const sep) (singleton id) |)

-------------------------------------------------------------------------------
-- Transformations: Zips and unzip
-------------------------------------------------------------------------------

zipWith : (a -> b -> c) -> Seq a -> Seq b -> Seq c
zipWith f nil _ = nil
zipWith f _ nil = nil
zipWith f as bs with uncons as | uncons bs
... | nothing | _ = nil
... | _ | nothing = nil
... | just (x , xs) | just (y , ys) = cons (f x y) (zipWith f xs ys)

zip : Seq a -> Seq b -> Seq (Tuple a b)
zip = zipWith _,_

-- Zips together a list of heads and a list of tails.
zipCons : Seq a -> Seq (Seq a) -> Seq (Seq a)
zipCons {a} heads tails =
    (zipWith cons heads (tails <> padding)) <> excess
  where
    -- Extra tails that will be zipped with those heads that have no
    -- corresponding tail in tails.
    padding : Seq (Seq a)
    padding = replicate (length heads - length tails) azero
    -- The tails that cannot be zipped because they have no corresponding
    -- head in heads.
    excess : Seq (Seq a)
    excess = snd (splitAt (length heads) tails)
