{-# OPTIONS --type-in-type #-}

module Data.Sequence where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Data.Constraint.Nonempty
open import Data.Monoid.Endo
open import Data.Foldable
open import Data.Sequence.Internal
open import Data.Traversable

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
    a b c : Set
    f : Set -> Set

-------------------------------------------------------------------------------
-- Seq
-------------------------------------------------------------------------------

data Seq (a : Set) : Set where
  Seq: : FingerTree (Elem a) -> Seq a

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

instance
  Semigroup-Seq : Semigroup (Seq a)
  Semigroup-Seq ._<>_ (Seq: xs) (Seq: ys) = Seq: (appendTree0 xs ys)

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

private
  bindSeq : Seq a -> (a -> Seq b) -> Seq b
  bindSeq xs f = foldl (\ ys x -> ys <> f x) mempty xs

instance
  Applicative-Seq : Applicative Seq
  Applicative-Seq .pure x = Seq: (Single (Elem: x))
  Applicative-Seq ._<*>_ fs xs =
    bindSeq xs (\ x -> bindSeq fs (\ f -> pure (f x)))

  Monad-Seq : Monad Seq
  Monad-Seq ._>>=_ = bindSeq

-------------------------------------------------------------------------------
-- Constructors
-------------------------------------------------------------------------------

cons : a -> Seq a -> Seq a
cons x (Seq: xs) = Seq: (Elem: x <| xs)

snoc : Seq a -> a -> Seq a
snoc (Seq: xs) x = Seq: (xs |> Elem: x)
{-
replicate : Nat -> a -> Seq a
replicate n x = runIdentity (replicateA n (Identity: x))

-------------------------------------------------------------------------------
-- Destructors
-------------------------------------------------------------------------------

uncons : Seq a -> Maybe (a * Seq a)
uncons = list Nothing (\ x xs -> Just (x , xs))

unsnoc : Seq a -> Maybe (Seq a * a)
unsnoc = foldr go Nothing
  where
    go : a -> Maybe (Seq a * a) -> Maybe (Seq a * a)
    go x Nothing = Just ([] , x)
    go x (Just (xs , e)) = Just (x :: xs , e)

head : Seq a -> Maybe a
head = list Nothing (\ x _ -> Just x)

tail : Seq a -> Maybe (Seq a)
tail = list Nothing (\ _ xs -> Just xs )

init : (xs : Seq a) {{_ : IsNonempty xs}} -> Seq a
init (x :: []) = []
init (x :: x' :: xs) = x :: init (x' :: xs)

-------------------------------------------------------------------------------
-- Transformations
-------------------------------------------------------------------------------

reverse : Seq a -> Seq a
reverse = foldl (flip cons) []

intersperse : a -> Seq a -> Seq a
intersperse sep = flip foldr [] \ where
  x [] -> [ x ]
  x xs -> x :: sep :: xs

-------------------------------------------------------------------------------
-- Extracting sublists
-------------------------------------------------------------------------------

takeWhile : (a -> Bool) -> Seq a -> Seq a
takeWhile _ [] = []
takeWhile p (x :: xs) = if p x then x :: takeWhile p xs else []

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

-------------------------------------------------------------------------------
-- Indexed functions
-------------------------------------------------------------------------------

indexed : Seq a -> Seq (Nat * a)
indexed [] = []
indexed xs = go 0 xs
  where
    go : Nat -> Seq a -> Seq (Nat * a)
    go _ [] = []
    go n (y :: ys) = (n , y) :: go (Suc n) ys

splitAt : Nat -> Seq a -> Seq a * Seq a
splitAt n xs = (take n xs , drop n xs)

at : Nat -> Seq a -> Maybe a
at n = leftToMaybe <<< flip foldlM 0 \
  k x -> if k == n then Left x else Right (Suc k)

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

-------------------------------------------------------------------------------
-- Searching with a predicate
-------------------------------------------------------------------------------

filter : (a -> Bool) -> Seq a -> Seq a
filter p = foldr (\ x xs -> if p x then x :: xs else xs) []

filterA : {{_ : Applicative f}} -> (a -> f Bool) -> Seq a -> f (Seq a)
filterA p = flip foldr (pure []) \ where
    x xs -> (| if_then_else_ (p x) (| (x ::_) xs |) xs |)

partition : (a -> Bool) -> Seq a -> Seq a * Seq a
partition p xs = (filter p xs , filter (not <<< p) xs)

-------------------------------------------------------------------------------
-- Segments
-------------------------------------------------------------------------------

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

-------------------------------------------------------------------------------
-- Scans
-------------------------------------------------------------------------------

scanl : (b -> a -> b) -> b -> Seq a -> Seq b
scanl f b xs = foldl f b <$> inits xs

scanr : (a -> b -> b) -> b -> Seq a -> Seq b
scanr f b xs = foldr f b <$> tails xs

-------------------------------------------------------------------------------
-- Zipping functions
-------------------------------------------------------------------------------

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
      g s a = let s' = dropWhile (_/= a) s in
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
groupBy eq [] = []
groupBy eq (x :: xs) = let (ys , zs) = span (eq x) xs in
  (x :: ys) :: groupBy eq zs

group : {{_ : Eq a}} -> Seq a -> Seq (Seq a)
group = groupBy _==_

-------------------------------------------------------------------------------
-- Transformations
-------------------------------------------------------------------------------

intercalate : {{_ : Monoid a}} -> a -> Seq a -> a
intercalate sep [] = mempty
intercalate sep (s :: []) = s
intercalate sep (s :: rest) = s <> sep <> intercalate sep rest

transpose : Seq (Seq a) -> Seq (Seq a)
transpose [] = []
transpose (heads :: tails) = zipCons heads (transpose tails)

-------------------------------------------------------------------------------
-- Set-like operations
-------------------------------------------------------------------------------

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

-------------------------------------------------------------------------------
-- Sorting
-------------------------------------------------------------------------------

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

-------------------------------------------------------------------------------
-- Searching
-------------------------------------------------------------------------------

lookup : {{_ : Eq a}} -> a -> Seq (a * b) -> Maybe b
lookup a [] = Nothing
lookup a ((a' , b) :: xs) = if a == a' then Just b else lookup a xs
-}
