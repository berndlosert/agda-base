{-# OPTIONS --type-in-type #-}

module Data.Sequence where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

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
    a b c v : Set
    f t : Set -> Set

-------------------------------------------------------------------------------
-- Seq
-------------------------------------------------------------------------------

abstract
  data Seq (a : Set) : Set where
    toSeq : FingerTree (Sum Nat) (Elem a) -> Seq a

  instance
    Semigroup-Seq : Semigroup (Seq a)
    Semigroup-Seq ._<>_ (toSeq l) (toSeq r) = toSeq (l <> r)

    Monoid-Seq : Monoid (Seq a)
    Monoid-Seq .mempty = toSeq Tree.empty

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
-- Constructors
-------------------------------------------------------------------------------

  cons : a -> Seq a -> Seq a
  cons x (toSeq xs) = toSeq (Tree.cons (toElem x) xs)

  snoc : Seq a -> a -> Seq a
  snoc (toSeq xs) x = toSeq (Tree.snoc xs (toElem x))

  singleton : a -> Seq a
  singleton x = toSeq (Tree.singleton (toElem x))

  fromList : List a -> Seq a
  fromList = foldr cons empty

  iterateN : Nat -> (a -> a) -> a -> Seq a
  iterateN 0 f x = empty
  iterateN 1 f x = singleton x
  iterateN (suc n) f x = cons (f x) (iterateN n f x)

  replicate : Nat -> a -> Seq a
  replicate n = iterateN n id

  replicateA : {{Applicative f}} -> Nat -> f a -> f (Seq a)
  replicateA {f} {a} n0 fa = loop n0
    where
      loop : Nat -> f (Seq a)
      loop 0 = pure empty
      loop (suc n) = (| cons fa (loop n) |)

-------------------------------------------------------------------------------
-- Destructors
-------------------------------------------------------------------------------

  uncons : Seq a -> Maybe (Pair a (Seq a))
  uncons (toSeq t) =
    case Tree.uncons t of \ where
      nothing -> nothing
      (just (toElem x , xs)) -> just (x , toSeq xs)

  unsnoc : Seq a -> Maybe (Pair (Seq a) a)
  unsnoc (toSeq t) =
    case Tree.unsnoc t of \ where
      nothing -> nothing
      (just (xs , toElem x)) -> just (toSeq xs , x)

  head : Seq a -> Maybe a
  head = map fst <<< uncons

  tail : Seq a -> Maybe (Seq a)
  tail = map snd <<< uncons

  init : Seq a -> Maybe (Seq a)
  init s = maybe nothing (just <<< fst) (unsnoc s)

-------------------------------------------------------------------------------
-- Transformations
-------------------------------------------------------------------------------

  reverse : Seq a -> Seq a
  reverse = foldl (flip cons) empty

  intersperse : a -> Seq a -> Seq a
  intersperse sep s =
    case uncons s of \ where
      nothing -> empty
      (just (x , xs)) -> cons x (| _#_ xs (cons (const sep) (singleton id)) |)

-------------------------------------------------------------------------------
-- Indexed folds
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
-- Searching with a predicate
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

  filter : (a -> Bool) -> Seq a -> Seq a
  filter {a} p = foldl go empty
    where
      go : Seq a -> a -> Seq a
      go xs x = if p x then snoc xs x else xs

  filterA : {{Applicative f}} -> (a -> f Bool) -> Seq a -> f (Seq a)
  filterA {f} {a} p = foldr go (pure empty)
    where
      go : a -> f (Seq a) -> f (Seq a)
      go x xs = (| if_then_else_ (p x) (| (cons x) xs |) xs |)

  partition : (a -> Bool) -> Seq a -> Pair (Seq a) (Seq a)
  partition {a} p = foldl go (empty , empty)
    where
      go : Pair (Seq a) (Seq a) -> a -> Pair (Seq a) (Seq a)
      go (xs , ys) x = if p x then (snoc xs x , ys) else (xs , snoc ys x)

-------------------------------------------------------------------------------
-- Indexed functions
-------------------------------------------------------------------------------

  splitAt : Nat -> Seq a -> Pair (Seq a) (Seq a)
  splitAt n (toSeq t) = bimap toSeq toSeq $ Tree.split (\ m -> n < getSum m) t

  at : Nat -> Seq a -> Maybe a
  at n xs = splitAt n xs # snd # head

  updateAt : Nat -> (a -> Maybe a) -> Seq a -> Seq a
  updateAt n f xs = let (l , r) = splitAt n xs in
    case uncons r of \ where
      nothing -> xs
      (just (x , r')) -> l <> maybe r' (flip cons r') (f x)

  deleteAt : Nat -> Seq a -> Seq a
  deleteAt n = updateAt n (const nothing)

  modifyAt : Nat -> (a -> a) -> Seq a -> Seq a
  modifyAt n f = updateAt n (f >>> just)

  setAt : Nat -> a -> Seq a -> Seq a
  setAt n x = modifyAt n (const x)

  insertAt : Nat -> a -> Seq a -> Seq a
  insertAt n x xs = let (l , r) = splitAt n xs in
    case uncons r of \ where
      nothing -> l <> singleton x
      _ -> l <> cons x r

-------------------------------------------------------------------------------
-- Extracting sublists
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

  take : Nat -> Seq a -> Seq a
  take n = fst <<< splitAt n

  drop : Nat -> Seq a -> Seq a
  drop n = snd <<< splitAt n

-------------------------------------------------------------------------------
-- Segments
-------------------------------------------------------------------------------

  inits : Seq a -> Seq (Seq a)
  inits (toSeq t) = cons empty (toSeq (Tree.inits (toElem <<< toSeq) t))

  tails : Seq a -> Seq (Seq a)
  tails (toSeq t) = snoc (toSeq (Tree.tails (toElem <<< toSeq) t))  empty

  segments : Seq a -> Seq (Seq a)
  segments xs = singleton empty <>
    (filter (not <<< null) $ foldr _<>_ empty (tails <$> inits xs))

  segmentsOfSize : Nat -> Seq a -> Seq (Seq a)
  segmentsOfSize 0 _ = singleton empty
  segmentsOfSize n xs =
    filter (\ ys -> length ys == n) $ foldr _<>_ empty (tails <$> inits xs)

-------------------------------------------------------------------------------
-- Scans
-------------------------------------------------------------------------------

  scanl : (b -> a -> b) -> b -> Seq a -> Seq b
  scanl f b xs = cons b (snd $ mapAccumL (\ x z -> dup (f x z)) b xs)

  scanr : (a -> b -> b) -> b -> Seq a -> Seq b
  scanr f b xs = snoc (snd $ mapAccumR (\ z x -> dup (f x z)) b xs) b

-------------------------------------------------------------------------------
-- Zipping functions
-------------------------------------------------------------------------------

  {-# TERMINATING #-}
  zipWith : (a -> b -> c) -> Seq a -> Seq b -> Seq c
  zipWith f as bs =
    case uncons as of \ where
      nothing -> empty
      (just (x , xs)) ->
        case uncons bs of \ where
          nothing -> empty
          (just (y , ys)) -> cons (f x y) (zipWith f xs ys)

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

-------------------------------------------------------------------------------
-- Predicates
-------------------------------------------------------------------------------

  module _ {{_ : Eq a}} where

    isPrefixOf : Seq a -> Seq a -> Bool
    isPrefixOf xs ys = take (length xs) ys == xs

    isSuffixOf : Seq a -> Seq a -> Bool
    isSuffixOf xs ys = isPrefixOf xs (drop (length xs) ys)

    isInfixOf : Seq a -> Seq a -> Bool
    isInfixOf xs ys = maybe false (const true) $
      find (_== xs) (segmentsOfSize (length xs) ys)

    isSubsequenceOf : Seq a -> Seq a -> Bool
    isSubsequenceOf xs ys = maybe false (const true) (foldlM g ys xs)
      where
        g : Seq a -> a -> Maybe (Seq a)
        g s a = let s' = dropWhileL (_/= a) s in
          if null s'
            then nothing
            else tail s'

-------------------------------------------------------------------------------
-- Sublists
-------------------------------------------------------------------------------

  stripPrefix : {{Eq a}} -> Seq a -> Seq a -> Maybe (Seq a)
  stripPrefix xs ys =
    if isPrefixOf xs ys then just (drop (length xs) ys) else nothing

  {-# TERMINATING #-}
  groupBy : (a -> a -> Bool) -> Seq a -> Seq (Seq a)
  groupBy eq as =
    case uncons as of \ where
      nothing -> empty
      (just (x , xs)) ->
        let (ys , zs) = spanl (eq x) xs
        in cons (cons x ys) (groupBy eq zs)

  group : {{Eq a}} -> Seq a -> Seq (Seq a)
  group = groupBy _==_

-------------------------------------------------------------------------------
-- Transformations
-------------------------------------------------------------------------------

  {-# TERMINATING #-} 
  intercalate : {{Monoid a}} -> a -> Seq a -> a
  intercalate sep as =
    case uncons as of \ where
      nothing -> mempty
      (just (a , as')) ->
        case uncons as' of \ where
          nothing -> a
          (just (x , xs)) -> a <> sep <> intercalate sep (cons x xs)

  {-# TERMINATING #-}
  transpose : Seq (Seq a) -> Seq (Seq a)
  transpose ass =
    case uncons ass of \ where
      nothing -> empty
      (just (heads , tails)) -> zipCons heads (transpose tails)

-------------------------------------------------------------------------------
-- Set-like operations
-------------------------------------------------------------------------------

  {-# TERMINATING #-}
  deleteBy : (a -> a -> Bool) -> a -> Seq a -> Seq a
  deleteBy eq x xs =
    case uncons xs of \ where
      nothing -> empty
      (just (y , ys)) ->
        if eq x y
          then ys
          else (cons y (deleteBy eq x ys))

  {-# TERMINATING #-}
  nubBy : (a -> a -> Bool) -> Seq a -> Seq a
  nubBy {a} eq l = nubBy' l empty
    where
      elemBy : (a -> a -> Bool) -> a -> Seq a -> Bool
      elemBy eq y ys =
        case uncons ys of \ where
           nothing -> false
           (just (x , xs)) -> eq x y || elemBy eq y xs

      nubBy' : Seq a -> Seq a -> Seq a
      nubBy' as xs =
        case uncons as of \ where
          nothing -> empty
          (just (y , ys)) ->
            if elemBy eq y xs
              then nubBy' ys xs
              else cons y (nubBy' ys (cons y xs))

  unionBy : (a -> a -> Bool) -> Seq a -> Seq a -> Seq a
  unionBy eq xs ys = xs <> foldl (flip (deleteBy eq)) (nubBy eq ys) ys

  module _ {{_ : Eq a}} where

    delete : a -> Seq a -> Seq a
    delete = deleteBy _==_

    nub : Seq a -> Seq a
    nub = nubBy _==_

    union : Seq a -> Seq a -> Seq a
    union = unionBy _==_

-------------------------------------------------------------------------------
-- Sorting
-------------------------------------------------------------------------------

  {-# TERMINATING #-}
  insertBy : (a -> a -> Ordering) -> a -> Seq a -> Seq a
  insertBy cmp x as =
    case uncons as of \ where
      nothing -> singleton x
      (just (y , xs)) ->
        case cmp x y of \ where
          LT -> cons x (cons y xs)
          _ -> cons y (insertBy cmp x xs)

  {-# TERMINATING #-}
  sortBy : (a -> a -> Ordering) -> Seq a -> Seq a
  sortBy cmp as =
    case uncons as of \ where
      nothing -> empty
      (just (x , xs)) -> insertBy cmp x (sortBy cmp xs)

  module _ {{_ : Ord a}} where

    insert : a -> Seq a -> Seq a
    insert = insertBy compare

    sort : Seq a -> Seq a
    sort = sortBy compare

    sortOn : (b -> a) -> Seq b -> Seq b
    sortOn f = map snd <<< sortBy (comparing fst) <<< map (pair f id)

-------------------------------------------------------------------------------
-- Searching
-------------------------------------------------------------------------------

  {-# TERMINATING #-}
  lookup : {{Eq a}} -> a -> Seq (Pair a b) -> Maybe b
  lookup a s =
    case uncons s of \ where
      nothing -> nothing
      (just ((a' , b) , xs)) -> if a == a' then just b else lookup a xs
