{-# OPTIONS --type-in-type #-}

module Data.List where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Data.Constraint.Nonempty
open import Data.Monoid.Endo
open import Data.Foldable
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
-- Constructors
-------------------------------------------------------------------------------

cons : a -> List a -> List a
cons = _::_

snoc : List a -> a -> List a
snoc xs x = xs <> [ x ]

iterateN : Nat -> (a -> a) -> a -> List a
iterateN 0 f x = []
iterateN 1 f x = [ x ]
iterateN (Suc n) f x = f x :: iterateN n f x

replicate : Nat -> a -> List a
replicate n = iterateN n id

replicateA : {{_ : Applicative f}} -> Nat -> f a -> f (List a)
replicateA {f} {a} n0 fa = loop n0
  where
    loop : Nat -> f (List a)
    loop 0 = pure []
    loop (Suc n) = (| _::_ fa (loop n) |)

-------------------------------------------------------------------------------
-- Destructors
-------------------------------------------------------------------------------

head : List a -> Maybe a
head = list Nothing (\ x _ -> Just x)

tail : List a -> Maybe (List a)
tail = list Nothing (\ _ xs -> Just xs )

uncons : List a -> Maybe (a * List a)
uncons = list Nothing (\ x xs -> Just (x , xs))

unsnoc : List a -> Maybe (List a * a)
unsnoc = foldr go Nothing
  where
    go : a -> Maybe (List a * a) -> Maybe (List a * a)
    go x Nothing = Just ([] , x)
    go x (Just (xs , e)) = Just (x :: xs , e)

init : (xs : List a) {{_ : IsNonempty xs}} -> List a
init (x :: []) = []
init (x :: x' :: xs) = x :: init (x' :: xs)

-------------------------------------------------------------------------------
-- Transformations
-------------------------------------------------------------------------------

reverse : List a -> List a
reverse = foldl (flip cons) []

intersperse : a -> List a -> List a
intersperse sep = flip foldr [] \ where
  x [] -> [ x ]
  x xs -> x :: sep :: xs

-------------------------------------------------------------------------------
-- Extracting sublists
-------------------------------------------------------------------------------

takeWhile : (a -> Bool) -> List a -> List a
takeWhile _ [] = []
takeWhile p (x :: xs) = if p x then x :: takeWhile p xs else []

dropWhile : (a -> Bool) -> List a -> List a
dropWhile _ [] = []
dropWhile p xs@(x :: xs') = if p x then dropWhile p xs' else xs

take : Nat -> List a -> List a
take _ [] = []
take 0 xs = []
take (Suc n) (x :: xs) = x :: take n xs

drop : Nat -> List a -> List a
drop _ [] = []
drop 0 xs = xs
drop (Suc n) (x :: xs) = drop n xs

span : (a -> Bool) -> List a -> List a * List a
span p xs = (takeWhile p xs , dropWhile p xs)

break : (a -> Bool) -> List a -> List a * List a
break p = span (not <<< p)

-------------------------------------------------------------------------------
-- Indexed functions
-------------------------------------------------------------------------------

indexed : List a -> List (Nat * a)
indexed [] = []
indexed xs = go 0 xs
  where
    go : Nat -> List a -> List (Nat * a)
    go _ [] = []
    go n (y :: ys) = (n , y) :: go (Suc n) ys

splitAt : Nat -> List a -> List a * List a
splitAt n xs = (take n xs , drop n xs)

at : Nat -> List a -> Maybe a
at n = leftToMaybe <<< flip foldlM 0 \
  k x -> if k == n then Left x else Right (Suc k)

infixl 9 _!!_
_!!_ : List a -> Nat -> Maybe a
_!!_ = flip at

updateAt : Nat -> (a -> Maybe a) -> List a -> List a
updateAt 0 f (x :: xs) with f x
... | Nothing = xs
... | Just x' = x' :: xs
updateAt (Suc n) f (x :: xs) = x :: updateAt n f xs
updateAt _ _ [] = []

deleteAt : Nat -> List a -> List a
deleteAt n = updateAt n (const Nothing)

modifyAt : Nat -> (a -> a) -> List a -> List a
modifyAt n f = updateAt n (f >>> Just)

setAt : Nat -> a -> List a -> List a
setAt n x = modifyAt n (const x)

insertAt : Nat -> a -> List a -> List a
insertAt 0 x (y :: ys) = x :: y :: ys
insertAt (Suc n) x (y :: ys) = y :: insertAt n x ys
insertAt _ _ [] = []

-------------------------------------------------------------------------------
-- Searching with a predicate
-------------------------------------------------------------------------------

filter : (a -> Bool) -> List a -> List a
filter p = foldr (\ x xs -> if p x then x :: xs else xs) []

filterA : {{_ : Applicative f}} -> (a -> f Bool) -> List a -> f (List a)
filterA p = flip foldr (pure []) \ where
    x xs -> (| if_then_else_ (p x) (| (x ::_) xs |) xs |)

partition : (a -> Bool) -> List a -> List a * List a
partition p xs = (filter p xs , filter (not <<< p) xs)

-------------------------------------------------------------------------------
-- Segments
-------------------------------------------------------------------------------

inits : List a -> List (List a)
inits = foldr (\ x ys -> [ [] ] <> map (x ::_) ys) [ [] ]

tails : List a -> List (List a)
tails [] = [ [] ]
tails xs@(_ :: xs') = [ xs ] <> tails xs'

segments : List a -> List (List a)
segments xs = [ [] ] <>
  (filter (not <<< null) $ foldr _<>_ [] (tails <$> inits xs))

segmentsOfSize : Nat -> List a -> List (List a)
segmentsOfSize 0 _ = [ [] ]
segmentsOfSize n xs =
  filter (\ ys -> length ys == n) $ foldr _<>_ [] (tails <$> inits xs)

-------------------------------------------------------------------------------
-- Scans
-------------------------------------------------------------------------------

scanl : (b -> a -> b) -> b -> List a -> List b
scanl f b xs = foldl f b <$> inits xs

scanr : (a -> b -> b) -> b -> List a -> List b
scanr f b xs = foldr f b <$> tails xs

-------------------------------------------------------------------------------
-- Zipping functions
-------------------------------------------------------------------------------

zipWith : (a -> b -> c) -> List a -> List b -> List c
zipWith f [] _ = []
zipWith f _ [] = []
zipWith f (x :: xs) (y :: ys) = f x y :: zipWith f xs ys

zip : List a -> List b -> List (a * b)
zip = zipWith _,_

-- Zips together a list of heads and a list of tails.
zipCons : List a -> List (List a) -> List (List a)
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

  isPrefixOf : List a -> List a -> Bool
  isPrefixOf xs ys = take (length xs) ys == xs

  isSuffixOf : List a -> List a -> Bool
  isSuffixOf xs ys = isPrefixOf xs (drop (length xs) ys)

  isInfixOf : List a -> List a -> Bool
  isInfixOf xs ys = maybe False (const True) $
    find (_== xs) (segmentsOfSize (length xs) ys)

  isSubsequenceOf : List a -> List a -> Bool
  isSubsequenceOf xs ys = maybe False (const True) (foldlM g ys xs)
    where
      g : List a -> a -> Maybe (List a)
      g s a = let s' = dropWhile (_/= a) s in
        if null s'
          then Nothing
          else tail s'

-------------------------------------------------------------------------------
-- Sublists
-------------------------------------------------------------------------------

stripPrefix : {{_ : Eq a}} -> List a -> List a -> Maybe (List a)
stripPrefix xs ys =
  if isPrefixOf xs ys then Just (drop (length xs) ys) else Nothing

{-# TERMINATING #-}
groupBy : (a -> a -> Bool) -> List a -> List (List a)
groupBy eq [] = []
groupBy eq (x :: xs) = let (ys , zs) = span (eq x) xs in
  (x :: ys) :: groupBy eq zs

group : {{_ : Eq a}} -> List a -> List (List a)
group = groupBy _==_

-------------------------------------------------------------------------------
-- Transformations
-------------------------------------------------------------------------------

intercalate : {{_ : Monoid a}} -> a -> List a -> a
intercalate sep [] = mempty
intercalate sep (s :: []) = s
intercalate sep (s :: rest) = s <> sep <> intercalate sep rest

transpose : List (List a) -> List (List a)
transpose [] = []
transpose (heads :: tails) = zipCons heads (transpose tails)

-------------------------------------------------------------------------------
-- Set-like operations
-------------------------------------------------------------------------------

deleteBy : (a -> a -> Bool) -> a -> List a -> List a
deleteBy _ _ [] = []
deleteBy eq x (y :: ys) = if eq x y then ys else (y :: deleteBy eq x ys)

nubBy : (a -> a -> Bool) -> List a -> List a
nubBy {a} eq l = nubBy' l []
  where
    elemBy : (a -> a -> Bool) -> a -> List a -> Bool
    elemBy _ _ [] = False
    elemBy eq y (x :: xs) = eq x y || elemBy eq y xs

    nubBy' : List a -> List a -> List a
    nubBy' [] _ = []
    nubBy' (y :: ys) xs =
      if elemBy eq y xs
      then nubBy' ys xs
      else (y :: nubBy' ys (y :: xs))

unionBy : (a -> a -> Bool) -> List a -> List a -> List a
unionBy eq xs ys = xs <> foldl (flip (deleteBy eq)) (nubBy eq ys) ys

module _ {{_ : Eq a}} where

  delete : a -> List a -> List a
  delete = deleteBy _==_

  nub : List a -> List a
  nub = nubBy _==_

  union : List a -> List a -> List a
  union = unionBy _==_

-------------------------------------------------------------------------------
-- Sorting
-------------------------------------------------------------------------------

insertBy : (a -> a -> Ordering) -> a -> List a -> List a
insertBy cmp x [] = x :: []
insertBy cmp x (y :: xs) with cmp x y
... | LT = x :: y :: xs
... | _ = y :: insertBy cmp x xs

sortBy : (a -> a -> Ordering) -> List a -> List a
sortBy cmp [] = []
sortBy cmp (x :: xs) = insertBy cmp x (sortBy cmp xs)

module _ {{_ : Ord a}} where

  insert : a -> List a -> List a
  insert = insertBy compare

  sort : List a -> List a
  sort = sortBy compare

  sortOn : (b -> a) -> List b -> List b
  sortOn f = map snd <<< sortBy (comparing fst) <<< map (tuple f id)

-------------------------------------------------------------------------------
-- Searching
-------------------------------------------------------------------------------

lookup : {{_ : Eq a}} -> a -> List (a * b) -> Maybe b
lookup a [] = Nothing
lookup a ((a' , b) :: xs) = if a == a' then Just b else lookup a xs
