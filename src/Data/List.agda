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

replicate : Nat -> a -> List a
replicate n x = applyN (x ::_) n []

-------------------------------------------------------------------------------
-- Destructors
-------------------------------------------------------------------------------

uncons : List a -> Maybe (a * List a)
uncons = list Nothing (\ x xs -> Just (x , xs))

head : List a -> Maybe a
head = list Nothing (\ x _ -> Just x)

tail : List a -> Maybe (List a)
tail = list Nothing (\ _ xs -> Just xs )

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
takeWhile p [] = []
takeWhile p (x :: xs) = if p x then x :: takeWhile p xs else []

dropWhile : (a -> Bool) -> List a -> List a
dropWhile p [] = []
dropWhile p xs@(x :: xs') = if p x then dropWhile p xs' else xs

take : Nat -> List a -> List a
take n [] = []
take 0 xs = []
take (Suc n) (x :: xs) = x :: take n xs

drop : Nat -> List a -> List a
drop n [] = []
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
indexed = reverse <<< flip foldl [] \ where
  [] a -> (0 , a) :: []
  xs@(h :: t) a' -> (Suc (fst h) , a') :: xs

splitAt : Nat -> List a -> List a * List a
splitAt n xs = (take n xs , drop n xs)

at : Nat -> List a -> Maybe a
at n = leftToMaybe <<< flip foldlM 0 \
  k x -> if k == n then Left x else Right (Suc k)

infixl 9 _!!_
_!!_ : List a -> Nat -> Maybe a
_!!_ = flip at

deleteAt : Nat -> List a -> List a
deleteAt n = reverse <<< snd <<< flip foldl (0 , []) \ where
  (k , xs) x -> (Suc k , (if k == n then xs else cons x xs))

modifyAt : Nat -> (a -> a) -> List a -> List a
modifyAt n f = reverse <<< snd <<< flip foldl (0 , []) \ where
  (k , xs) x -> (Suc k , (if k == n then cons (f x) xs else cons x xs))

setAt : Nat -> a -> List a -> List a
setAt n x = modifyAt n (const x)

insertAt : Nat -> a -> List a -> List a
insertAt n x' = reverse <<< snd <<< flip foldl (0 , []) \ where
  (k , xs) x -> (Suc k , (if k == n then x' :: x :: xs else x :: xs))

-------------------------------------------------------------------------------
-- Searching with a predicate
-------------------------------------------------------------------------------

filter : (a -> Bool) -> List a -> List a
filter p = foldr (\ x xs -> if p x then x :: xs else xs) []

partition : (a -> Bool) -> List a -> List a * List a
partition p xs = (filter p xs , filter (not <<< p) xs)

-------------------------------------------------------------------------------
-- Segments
-------------------------------------------------------------------------------

inits : List a -> List (List a)
inits = foldr (\ x ys -> [ [] ] <> map (x ::_) ys) [ [] ]

tails : List a -> List (List a)
tails = foldl (\ ys x -> map (flip snoc x) ys <> [ [] ]) [ [] ]

segments : List a -> List (List a)
segments xs = [ [] ] <>
  (filter (not <<< null) $ foldr _<>_ [] (tails <$> inits xs))

segmentsOfSize : Nat -> List a -> List (List a)
segmentsOfSize 0 _ = [ [] ]
segmentsOfSize n xs =
  filter (\ ys -> count ys == n) $ foldr _<>_ [] (tails <$> inits xs)

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
    padding = replicate (count heads - count tails) []
    -- The tails that cannot be zipped because they have no corresponding
    -- head in heads.
    excess = snd (splitAt (count heads) tails)

-------------------------------------------------------------------------------
-- Predicates
-------------------------------------------------------------------------------

isPrefixOf : {{_ : Eq a}} -> List a -> List a -> Bool
isPrefixOf xs ys = take (count xs) ys == xs

isSuffixOf : {{_ : Eq a}} -> List a -> List a -> Bool
isSuffixOf xs ys = isPrefixOf xs (drop (count xs) ys)

isInfixOf : {{_ : Eq a}} -> List a -> List a -> Bool
isInfixOf xs ys = maybe False (const True) $
  find (_== xs) (segmentsOfSize (count xs) ys)

isSubsequenceOf : {{_ : Eq a}} -> List a -> List a -> Bool
isSubsequenceOf xs ys = maybe False (const True) (foldlM g ys xs)
  where
    g : {{_ : Eq a}} -> List a -> a -> Maybe (List a)
    g s a = let s' = dropWhile (_/= a) s in
      if null s'
        then Nothing
        else tail s'

-------------------------------------------------------------------------------
-- Sublists
-------------------------------------------------------------------------------

stripPrefix : {{_ : Eq a}} -> List a -> List a -> Maybe (List a)
stripPrefix xs ys =
  if isPrefixOf xs ys then Just (drop (count xs) ys) else Nothing

{-# TERMINATING #-}
groupBy : (a -> a -> Bool) -> List a -> List (List a)
groupBy eq xs = case uncons xs of \ where
  Nothing -> []
  (Just (x , xs)) -> let (ys , zs) = span (eq x) xs in
    cons x ys :: groupBy eq zs

group : {{_ : Eq a}} -> List a -> List (List a)
group = groupBy _==_

-------------------------------------------------------------------------------
-- Filtering functions
-------------------------------------------------------------------------------

filterA : {{_ : Applicative f}} -> (a -> f Bool) -> List a -> f (List a)
filterA p = flip foldr (pure []) \ where
    x xs -> (| if_then_else_ (p x) (| (x ::_) xs |) xs |)

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

delete : {{_ : Eq a}} -> a -> List a -> List a
delete = deleteBy _==_

nub : {{_ : Eq a}} -> List a -> List a
nub = nubBy _==_

union : {{_ : Eq a}} -> List a -> List a -> List a
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

insert : {{_ : Ord a}} -> a -> List a -> List a
insert = insertBy compare

sort : {{_ : Ord a}} -> List a -> List a
sort = sortBy compare

sortOn : {{_ : Ord b}} -> (a -> b) -> List a -> List a
sortOn f = map snd <<< sortBy (comparing fst) <<< map (tuple f id)

-------------------------------------------------------------------------------
-- Searching
-------------------------------------------------------------------------------

lookup : {{_ : Eq a}} -> a -> List (a * b) -> Maybe b
lookup a [] = Nothing
lookup a ((a' , b) :: xs) = if a == a' then Just b else lookup a xs
