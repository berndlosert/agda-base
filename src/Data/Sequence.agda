{-# OPTIONS --type-in-type #-}

module Data.Sequence where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Control.Alternative
open import Data.Constraint.Nonempty
open import Data.Monoid.Endo
open import Data.Monoid.Sum
open import Data.Foldable
open import Data.Traversable
open import Data.FingerTree as Tree using (FingerTree)
open import Data.Sequence.Elem
open import Data.Sequence.View

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

data Seq (a : Set) : Set where
  Seq: : FingerTree (Sum Nat) (Elem a) -> Seq a

viewl : Seq a -> ViewL Seq a
viewl (Seq: t) with Tree.viewl t
... | EmptyL = EmptyL
... | (Elem: x) :< xs = x :< (Seq: xs)

viewr : Seq a -> ViewR Seq a
viewr (Seq: t) with Tree.viewr t
... | EmptyR = EmptyR
... | xs :> (Elem: x) = Seq: xs :> x

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

instance
  {-# TERMINATING #-}
  Eq-Seq : {{_ : Eq a}} -> Eq (Seq a)
  Eq-Seq ._==_ l r with viewl l | viewl r
  ... | EmptyL | EmptyL = True
  ... | EmptyL | _ = False
  ... | _ | EmptyL = False
  ... | x :< xs | y :< ys = x == y && xs == ys

  Semigroup-Seq : Semigroup (Seq a)
  Semigroup-Seq ._<>_ (Seq: l) (Seq: r) = Seq: (l <> r)

  Monoid-Seq : Monoid (Seq a)
  Monoid-Seq .mempty = Seq: Tree.empty

  Foldable-Seq : Foldable Seq
  Foldable-Seq .foldMap f (Seq: t) = foldMap (f <<< getElem) t

  Functor-Seq : Functor Seq
  Functor-Seq .map f (Seq: t) = Seq: (map (map f) t)

  Applicative-Seq : Applicative Seq
  Applicative-Seq .pure = Seq: <<< Tree.singleton <<< Elem:
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
  Traversable-Seq .traverse f (Seq: t) = Seq: <$> traverse (traverse f) t

  NonemptyConstraint-Seq : NonemptyConstraint (Seq a)
  NonemptyConstraint-Seq .IsNonempty (Seq: t) = IsNonempty t

-------------------------------------------------------------------------------
-- Constructors
-------------------------------------------------------------------------------

cons : a -> Seq a -> Seq a
cons x (Seq: xs) = Seq: (Tree.cons (Elem: x) xs)

snoc : Seq a -> a -> Seq a
snoc (Seq: xs) x = Seq: (Tree.snoc xs (Elem: x))

singleton : a -> Seq a
singleton x = Seq: (Tree.singleton (Elem: x))

fromList : List a -> Seq a
fromList = foldr cons empty

iterateN : Nat -> (a -> a) -> a -> Seq a
iterateN 0 f x = empty
iterateN 1 f x = singleton x
iterateN (Suc n) f x = cons (f x) (iterateN n f x)

replicate : Nat -> a -> Seq a
replicate n = iterateN n id

replicateA : {{_ : Applicative f}} -> Nat -> f a -> f (Seq a)
replicateA {f} {a} n0 fa = loop n0
  where
    loop : Nat -> f (Seq a)
    loop 0 = pure empty
    loop (Suc n) = (| cons fa (loop n) |)

-------------------------------------------------------------------------------
-- Destructors
-------------------------------------------------------------------------------

uncons : Seq a -> Maybe (a * Seq a)
uncons s with viewl s
... | EmptyL = Nothing
... | x :< xs = Just (x , xs)

head : Seq a -> Maybe a
head = map fst <<< uncons

tail : Seq a -> Maybe (Seq a)
tail = map snd <<< uncons

unsnoc : Seq a -> Maybe (Seq a * a)
unsnoc s with viewr s
... | EmptyR = Nothing
... | xs :> x = Just (xs , x)

init : (s : Seq a) {{_ : IsNonempty s}} -> Seq a
init s with viewr s
... | EmptyR = undefined -- No worries, this is impossible.
... | xs :> _ = xs

-------------------------------------------------------------------------------
-- Transformations
-------------------------------------------------------------------------------

reverse : Seq a -> Seq a
reverse = foldl (flip cons) empty

intersperse : a -> Seq a -> Seq a
intersperse sep s with viewl s
... | EmptyL = empty
... | x :< xs = cons x (xs <**> cons (const sep) (singleton id))

-------------------------------------------------------------------------------
-- Indexed folds
-------------------------------------------------------------------------------

ifoldr : (Nat -> a -> b -> b) -> b -> Seq a -> b
ifoldr f z xs = foldr (\ x g n -> f n x (g (Suc n))) (const z) xs 0

ifoldl : (b -> Nat -> a -> b) -> b -> Seq a -> b
ifoldl f z xs =
  foldl (\ g x n -> f (g (n - 1)) n x) (const z) xs (length xs - 1)

-------------------------------------------------------------------------------
-- Searching with a predicate
-------------------------------------------------------------------------------

indicesl : (a -> Bool) -> Seq a -> List Nat
indicesl p = ifoldr (\ n x ns -> if p x then n :: ns else ns) []

indicesr : (a -> Bool) -> Seq a -> List Nat
indicesr p = ifoldl (\ ns n x -> if p x then n :: ns else ns) []

filter : (a -> Bool) -> Seq a -> Seq a
filter p = foldl (\ xs x -> if p x then snoc xs x else xs) empty

filterA : {{_ : Applicative f}} -> (a -> f Bool) -> Seq a -> f (Seq a)
filterA p = flip foldr (pure empty) \ where
    x xs -> (| if_then_else_ (p x) (| (cons x) xs |) xs |)

partition : (a -> Bool) -> Seq a -> Seq a * Seq a
partition p = flip foldl (empty , empty) \ where
  (xs , ys) x -> if p x then (snoc xs x , ys) else (xs , snoc ys x)

-------------------------------------------------------------------------------
-- Indexed functions
-------------------------------------------------------------------------------

splitAt : Nat -> Seq a -> Seq a * Seq a
splitAt n (Seq: t) = bimap Seq: Seq: $ Tree.split (\ m -> n < getSum m) t

at : Nat -> Seq a -> Maybe a
at n xs = splitAt n xs # snd # head

infixl 9 _!!_
_!!_ : Seq a -> Nat -> Maybe a
_!!_ = flip at

updateAt : Nat -> (a -> Maybe a) -> Seq a -> Seq a
updateAt n f xs = let (l , r) = splitAt n xs in
  case viewl r of \ where
    EmptyL -> xs
    (x :< r') -> l <> maybe r' (flip cons r') (f x)

deleteAt : Nat -> Seq a -> Seq a
deleteAt n = updateAt n (const Nothing)

modifyAt : Nat -> (a -> a) -> Seq a -> Seq a
modifyAt n f = updateAt n (f >>> Just)

setAt : Nat -> a -> Seq a -> Seq a
setAt n x = modifyAt n (const x)

insertAt : Nat -> a -> Seq a -> Seq a
insertAt n x xs = let (l , r) = splitAt n xs in
  case viewl r of \ where
    EmptyL -> l <> singleton x
    _ -> l <> cons x r

-------------------------------------------------------------------------------
-- Extracting sublists
-------------------------------------------------------------------------------

breakl : (a -> Bool) -> Seq a -> Seq a * Seq a
breakl p xs = foldr (\ n _ -> splitAt n xs) (xs , empty) (indicesl p xs)

breakr : (a -> Bool) -> Seq a -> Seq a * Seq a
breakr p xs =
  foldr (\ n _ -> swap (splitAt (Suc n) xs)) (xs , empty) (indicesr p xs)

spanl : (a -> Bool) -> Seq a -> Seq a * Seq a
spanl p = breakl (not <<< p)

spanr : (a -> Bool) -> Seq a -> Seq a * Seq a
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
inits (Seq: t) = cons empty (Seq: (Tree.inits (Elem: <<< Seq:) t))

tails : Seq a -> Seq (Seq a)
tails (Seq: t) = snoc (Seq: (Tree.tails (Elem: <<< Seq:) t))  empty

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
scanl f b xs = cons b (snd $ mapAccumL (\ x z -> dupe (f x z)) b xs)

scanr : (a -> b -> b) -> b -> Seq a -> Seq b
scanr f b xs = snoc (snd $ mapAccumR (\ z x -> dupe (f x z)) b xs) b

-------------------------------------------------------------------------------
-- Zipping functions
-------------------------------------------------------------------------------

{-# TERMINATING #-}
zipWith : (a -> b -> c) -> Seq a -> Seq b -> Seq c
zipWith f as bs with viewl as | viewl bs
... | EmptyL | _ = empty
... | _ | EmptyL = empty
... | x :< xs | y :< ys = cons (f x y) (zipWith f xs ys)

zip : Seq a -> Seq b -> Seq (a * b)
zip = zipWith _,_

-- Zips together a list of heads and a list of tails.
zipCons : Seq a -> Seq (Seq a) -> Seq (Seq a)
zipCons heads tails =
    (zipWith cons heads (tails <> padding)) <> excess
  where
    -- Extra tails that will be zipped with those heads that have no
    -- corresponding tail in tails.
    padding = replicate (length heads - length tails) empty
    -- The tails that cannot be zipped because they have no corresponding
    -- head in heads.
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
  isInfixOf xs ys = maybe False (const True) $
    find (_== xs) (segmentsOfSize (length xs) ys)

  isSubsequenceOf : Seq a -> Seq a -> Bool
  isSubsequenceOf xs ys = maybe False (const True) (foldlM g ys xs)
    where
      g : Seq a -> a -> Maybe (Seq a)
      g s a = let s' = dropWhileL (_/= a) s in
        if null s'
          then Nothing
          else tail s'

-------------------------------------------------------------------------------
-- Sublists
-------------------------------------------------------------------------------

stripPrefix : {{_ : Eq a}} -> Seq a -> Seq a -> Maybe (Seq a)
stripPrefix xs ys =
  if isPrefixOf xs ys then Just (drop (length xs) ys) else Nothing

{-# TERMINATING #-}
groupBy : (a -> a -> Bool) -> Seq a -> Seq (Seq a)
groupBy eq as with viewl as
... | EmptyL = empty
... | x :< xs = let (ys , zs) = spanl (eq x) xs in
  cons (cons x ys) (groupBy eq zs)

group : {{_ : Eq a}} -> Seq a -> Seq (Seq a)
group = groupBy _==_

-------------------------------------------------------------------------------
-- Transformations
-------------------------------------------------------------------------------

{-# TERMINATING #-} 
intercalate : {{_ : Monoid a}} -> a -> Seq a -> a
intercalate sep as with viewl as
... | EmptyL = mempty
... | a :< as' = case viewl as' of \ where
  EmptyL -> a
  (x :< xs) -> a <> sep <> intercalate sep (cons x xs)

{-# TERMINATING #-}
transpose : Seq (Seq a) -> Seq (Seq a)
transpose ass with viewl ass
... | EmptyL = empty
... | heads :< tails = zipCons heads (transpose tails)

-------------------------------------------------------------------------------
-- Set-like operations
-------------------------------------------------------------------------------
{-
deleteBy : (a -> a -> Bool) -> a -> Seq a -> Seq a
deleteBy _ _ [] = []
deleteBy eq x (y :: ys) = if eq x y then ys else (y :: deleteBy eq x ys)

nubBy : (a -> a -> Bool) -> Seq a -> Seq a
nubBy {a} eq l = nubBy' l []
  where
    elemBy : (a -> a -> Bool) -> a -> Seq a -> Bool
    elemBy _ _ [] = False
    elemBy eq y (x :: xs) = eq x y || elemBy eq y xs

    nubBy' : Seq a -> Seq a -> Seq a
    nubBy' [] _ = []
    nubBy' (y :: ys) xs =
      if elemBy eq y xs
      then nubBy' ys xs
      else (y :: nubBy' ys (y :: xs))

unionBy : (a -> a -> Bool) -> Seq a -> Seq a -> Seq a
unionBy eq xs ys = xs <> foldl (flip (deleteBy eq)) (nubBy eq ys) ys

module _ {{_ : Eq a}} where

  delete : a -> Seq a -> Seq a
  delete = deleteBy _==_

  nub : Seq a -> Seq a
  nub = nubBy _==_

  union : Seq a -> Seq a -> Seq a
  union = unionBy _==_
-}
-------------------------------------------------------------------------------
-- Sorting
-------------------------------------------------------------------------------
{-
insertBy : (a -> a -> Ordering) -> a -> Seq a -> Seq a
insertBy cmp x [] = x :: []
insertBy cmp x (y :: xs) with cmp x y
... | LT = x :: y :: xs
... | _ = y :: insertBy cmp x xs

sortBy : (a -> a -> Ordering) -> Seq a -> Seq a
sortBy cmp [] = []
sortBy cmp (x :: xs) = insertBy cmp x (sortBy cmp xs)

module _ {{_ : Ord a}} where

  insert : a -> Seq a -> Seq a
  insert = insertBy compare

  sort : Seq a -> Seq a
  sort = sortBy compare

  sortOn : (b -> a) -> Seq b -> Seq b
  sortOn f = map snd <<< sortBy (comparing fst) <<< map (tuple f id)
-}
-------------------------------------------------------------------------------
-- Searching
-------------------------------------------------------------------------------

{-# TERMINATING #-}
lookup : {{_ : Eq a}} -> a -> Seq (a * b) -> Maybe b
lookup a s with viewl s
... | EmptyL = Nothing
... | (a' , b) :< xs = if a == a' then Just b else lookup a xs
