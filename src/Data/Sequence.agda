{-# OPTIONS --type-in-type #-}

module Data.Sequence where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Data.Constraint.Nonempty
open import Data.Monoid.Endo
open import Data.Monoid.Sum
open import Data.Foldable
open import Data.Traversable
open import Data.FingerTree as Tree hiding (cons; snoc; viewl; viewr)
open import Data.FingerTree.Digit
open import Data.FingerTree.Measured
open import Data.FingerTree.Node
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

data Seq (a : Set) : Set where
  Seq: : FingerTree (Sum Nat) (Elem a) -> Seq a

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

instance
  Semigroup-Seq : Semigroup (Seq a)
  Semigroup-Seq ._<>_ (Seq: xs) (Seq: ys) = Seq: (xs <> ys)

  Monoid-Seq : Monoid (Seq a)
  Monoid-Seq .mempty = Seq: Empty

  Functor-Seq : Functor Seq
  Functor-Seq .map f (Seq: xs) = Seq: (map (map f) xs)

  Foldable-Seq : Foldable Seq
  Foldable-Seq .foldMap f (Seq: xs) = foldMap (f <<< getElem) xs

  Traversable-Seq : Traversable Seq
  Traversable-Seq .traverse f seq with seq
  ... | Seq: Empty = pure (Seq: Empty)
  ... | Seq: (Single (Elem: x)) = (| (Seq: <<< Single <<< Elem:) (f x) |)
  ... | Seq: (Deep s pr m sf) = (|
      (\ pr' m' sf' -> Seq: (Deep s pr' m' sf'))
      (traverseDE f pr)
      (traverse (traverseNE f) m)
      (traverseDE f sf)
    |)

  Applicative-Seq : Applicative Seq
  Applicative-Seq .pure x = Seq: (Single (Elem: x))
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

  NonemptyConstraint-Seq : NonemptyConstraint (Seq a)
  NonemptyConstraint-Seq .IsNonempty (Seq: Empty) = Void
  NonemptyConstraint-Seq .IsNonempty _ = Unit

-------------------------------------------------------------------------------
-- Constructors
-------------------------------------------------------------------------------

cons : a -> Seq a -> Seq a
cons x (Seq: xs) = Seq: (Tree.cons (Elem: x) xs)

snoc : Seq a -> a -> Seq a
snoc (Seq: xs) x = Seq: (Tree.snoc xs (Elem: x))

singleton : a -> Seq a
singleton x = Seq: (Single (Elem: x))

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

viewl : Seq a -> ViewL Seq a
viewl (Seq: t) with Tree.viewl t
... | EmptyL = EmptyL
... | (Elem: x) :< xs = x :< (Seq: xs)

viewr : Seq a -> ViewR Seq a
viewr (Seq: t) with Tree.viewr t
... | EmptyR = EmptyR
... | xs :> (Elem: x) = Seq: xs :> x

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

{-# TERMINATING #-}
init : (s : Seq a) {{_ : IsNonempty s}} -> Seq a
init s with viewl s
... | EmptyL = undefined -- No worries, this is impossible.
... | x :< (Seq: Empty) = empty
... | x :< xs = cons x (init xs {{believeMe}})

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
-- Indexed functions
-------------------------------------------------------------------------------

--indexed : Seq a -> Seq (Nat * a)
--indexed [] = []
--indexed xs = go 0 xs
--  where
--    go : Nat -> Seq a -> Seq (Nat * a)
--    go _ [] = []
--    go n (y :: ys) = (n , y) :: go (Suc n) ys

splitAt : Nat -> Seq a -> Seq a * Seq a
splitAt n (Seq: t) = bimap Seq: Seq: $ Tree.split (\ m -> n < getSum m) t

at : Nat -> Seq a -> Maybe a
at n xs@(Seq: t) with n < length xs
... | False = Nothing
... | True = case Tree.splitTree (\ m -> n < getSum m) (Sum: 0) t {{believeMe}} of \ where
  (_ , x , _) -> Just (getElem x)
{-
infixl 9 _!!_
_!!_ : Seq a -> Nat -> Maybe a
_!!_ = flip at

deleteAt : Nat -> Seq a -> Seq a
deleteAt 0 (_ :: xs) = xs
deleteAt (Suc n) (x :: xs) = x :: deleteAt n xs
deleteAt _ [] = []

modifyAt : Nat -> (a -> a) -> Seq a -> Seq a
modifyAt 0 f (x :: xs) = f x :: xs
modifyAt (Suc n) f (x :: xs) = x :: modifyAt n f xs
modifyAt _ _ [] = []

setAt : Nat -> a -> Seq a -> Seq a
setAt n x = modifyAt n (const x)

updateAt : Nat -> (a -> Maybe a) -> Seq a -> Seq a
updateAt 0 f (x :: xs) with f x
... | Nothing = xs
... | Just x' = x' :: xs
updateAt (Suc n) f (x :: xs) = x :: updateAt n f xs
updateAt _ _ [] = []

insertAt : Nat -> a -> Seq a -> Seq a
insertAt 0 x (y :: ys) = x :: y :: ys
insertAt (Suc n) x (y :: ys) = y :: insertAt n x ys
insertAt _ _ [] = []
-}
-------------------------------------------------------------------------------
-- Extracting sublists
-------------------------------------------------------------------------------

{-# TERMINATING #-}
takeWhile : (a -> Bool) -> Seq a -> Seq a
takeWhile p s with viewl s
... | EmptyL = empty
... | x :< xs = if p x then cons x (takeWhile p xs) else empty
{-
dropWhile : (a -> Bool) -> Seq a -> Seq a
dropWhile _ [] = []
dropWhile p xs@(x :: xs') = if p x then dropWhile p xs' else xs

take : Nat -> Seq a -> Seq a
take _ [] = []
take 0 xs = []
take (Suc n) (x :: xs) = x :: take n xs

drop : Nat -> Seq a -> Seq a
drop _ [] = []
drop 0 xs = xs
drop (Suc n) (x :: xs) = drop n xs

span : (a -> Bool) -> Seq a -> Seq a * Seq a
span p xs = (takeWhile p xs , dropWhile p xs)

break : (a -> Bool) -> Seq a -> Seq a * Seq a
break p = span (not <<< p)
-}
-------------------------------------------------------------------------------
-- Searching with a predicate
-------------------------------------------------------------------------------
{-
filter : (a -> Bool) -> Seq a -> Seq a
filter p = foldr (\ x xs -> if p x then x :: xs else xs) []

filterA : {{_ : Applicative f}} -> (a -> f Bool) -> Seq a -> f (Seq a)
filterA p = flip foldr (pure []) \ where
    x xs -> (| if_then_else_ (p x) (| (x ::_) xs |) xs |)

partition : (a -> Bool) -> Seq a -> Seq a * Seq a
partition p xs = (filter p xs , filter (not <<< p) xs)
-}
-------------------------------------------------------------------------------
-- Segments
-------------------------------------------------------------------------------
{-
inits : Seq a -> Seq (Seq a)
inits = foldr (\ x ys -> [ [] ] <> map (x ::_) ys) [ [] ]

tails : Seq a -> Seq (Seq a)
tails [] = [ [] ]
tails xs@(_ :: xs') = [ xs ] <> tails xs'

segments : Seq a -> Seq (Seq a)
segments xs = [ [] ] <>
  (filter (not <<< null) $ foldr _<>_ [] (tails <$> inits xs))

segmentsOfSize : Nat -> Seq a -> Seq (Seq a)
segmentsOfSize 0 _ = [ [] ]
segmentsOfSize n xs =
  filter (\ ys -> length ys == n) $ foldr _<>_ [] (tails <$> inits xs)
-}
-------------------------------------------------------------------------------
-- Scans
-------------------------------------------------------------------------------
{-
scanl : (b -> a -> b) -> b -> Seq a -> Seq b
scanl f b xs = foldl f b <$> inits xs

scanr : (a -> b -> b) -> b -> Seq a -> Seq b
scanr f b xs = foldr f b <$> tails xs
-}
-------------------------------------------------------------------------------
-- Zipping functions
-------------------------------------------------------------------------------
{-
zipWith : (a -> b -> c) -> Seq a -> Seq b -> Seq c
zipWith f [] _ = []
zipWith f _ [] = []
zipWith f (x :: xs) (y :: ys) = f x y :: zipWith f xs ys

zip : Seq a -> Seq b -> Seq (a * b)
zip = zipWith _,_

-- Zips together a list of heads and a list of tails.
zipCons : Seq a -> Seq (Seq a) -> Seq (Seq a)
zipCons heads tails =
    (zipWith _::_ heads (tails <> padding)) <> excess
  where
    -- Extra tails that will be zipped with those heads that have no
    -- corresponding tail in tails.
    padding = replicate (length heads - length tails) []
    -- The tails that cannot be zipped because they have no corresponding
    -- head in heads.
    excess = snd (splitAt (length heads) tails)
-}
-------------------------------------------------------------------------------
-- Predicates
-------------------------------------------------------------------------------
{-
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
      g s a = let s' = dropWhile (_/= a) s in
        if null s'
          then Nothing
          else tail s'
-}
-------------------------------------------------------------------------------
-- Sublists
-------------------------------------------------------------------------------
{-
stripPrefix : {{_ : Eq a}} -> Seq a -> Seq a -> Maybe (Seq a)
stripPrefix xs ys =
  if isPrefixOf xs ys then Just (drop (length xs) ys) else Nothing

{-# TERMINATING #-}
groupBy : (a -> a -> Bool) -> Seq a -> Seq (Seq a)
groupBy eq [] = []
groupBy eq (x :: xs) = let (ys , zs) = span (eq x) xs in
  (x :: ys) :: groupBy eq zs

group : {{_ : Eq a}} -> Seq a -> Seq (Seq a)
group = groupBy _==_
-}
-------------------------------------------------------------------------------
-- Transformations
-------------------------------------------------------------------------------
{-
intercalate : {{_ : Monoid a}} -> a -> Seq a -> a
intercalate sep [] = mempty
intercalate sep (s :: []) = s
intercalate sep (s :: rest) = s <> sep <> intercalate sep rest

transpose : Seq (Seq a) -> Seq (Seq a)
transpose [] = []
transpose (heads :: tails) = zipCons heads (transpose tails)
-}
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
{-
lookup : {{_ : Eq a}} -> a -> Seq (a * b) -> Maybe b
lookup a [] = Nothing
lookup a ((a' , b) :: xs) = if a == a' then Just b else lookup a xs
-}
