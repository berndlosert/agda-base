{-# OPTIONS --type-in-type #-}

module Data.List where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Control.Monad.Free.General
open import Data.Monoid.Endo
open import Data.Filterable
open import Data.Foldable
open import Data.Traversable

-------------------------------------------------------------------------------
-- Re-exports
-------------------------------------------------------------------------------

open Data.Filterable public
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

singleton : a -> List a
singleton = _:: []

cons : a -> List a -> List a
cons = _::_

snoc : List a -> a -> List a
snoc xs x = xs <> singleton x

iterateN : Nat -> (a -> a) -> a -> List a
iterateN 0 f x = []
iterateN 1 f x = singleton x
iterateN (Suc n) f x = f x :: iterateN n f x

replicate : Nat -> a -> List a
replicate n = iterateN n id

replicateA : {{Applicative f}} -> Nat -> f a -> f (List a)
replicateA {f} {a} n0 fa = loop n0
  where
    loop : Nat -> f (List a)
    loop 0 = pure []
    loop (Suc n) = (| _::_ fa (loop n) |)

build : (forall {b} -> (a -> b -> b) -> b -> b) -> List a
build g = g _::_ []

-------------------------------------------------------------------------------
-- Destructors
-------------------------------------------------------------------------------

head : {{Partial}} -> List a -> a
head [] = undefined
head (x :: _) = x

tail : {{Partial}} -> List a -> List a
tail [] = undefined
tail (_ :: xs) = xs

uncons : List a -> Maybe (Pair a (List a))
uncons [] = Nothing
uncons (x :: xs) = Just (x , xs)

unsnoc : List a -> Maybe (Pair (List a) a)
unsnoc = foldr go Nothing
  where
    go : a -> Maybe (Pair (List a) a) -> Maybe (Pair (List a) a)
    go x Nothing = Just ([] , x)
    go x (Just (xs , e)) = Just (x :: xs , e)

init : {{Partial}} -> List a -> List a
init [] = undefined
init (x :: []) = []
init (x :: x' :: xs) = x :: init (x' :: xs)

-------------------------------------------------------------------------------
-- Transformations
-------------------------------------------------------------------------------

reverse : List a -> List a
reverse = foldl (flip cons) []

intersperse : a -> List a -> List a
intersperse {a} sep = foldr go []
  where
    go : a -> List a -> List a
    go x [] = singleton x
    go x xs = x :: sep :: xs

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

span : (a -> Bool) -> List a -> Pair (List a) (List a)
span p xs = (takeWhile p xs , dropWhile p xs)

break : (a -> Bool) -> List a -> Pair (List a) (List a)
break p = span (not <<< p)

-------------------------------------------------------------------------------
-- Indexed functions
-------------------------------------------------------------------------------

indexed : List a -> List (Pair Nat a)
indexed [] = []
indexed xs = go 0 xs
  where
    go : Nat -> List a -> List (Pair Nat a)
    go _ [] = []
    go n (y :: ys) = (n , y) :: go (Suc n) ys

splitAt : Nat -> List a -> Pair (List a) (List a)
splitAt n xs = (take n xs , drop n xs)

at : {{Partial}} -> Nat -> List a -> a
at 0 xs = head xs
at (Suc n) [] = undefined
at (Suc n) (x :: xs) = at n xs

updateAt : Nat -> (a -> Maybe a) -> List a -> List a
updateAt 0 f (x :: xs) = maybe xs (_:: xs) (f x)
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
-- Segments
-------------------------------------------------------------------------------

inits : List a -> List (List a)
inits {a} = foldr go (singleton [])
  where
    go : a -> List (List a) -> List (List a)
    go x xss = [] :: map (x ::_) xss

tails : List a -> List (List a)
tails [] = singleton []
tails xs@(_ :: xs') = xs :: tails xs'

segments : List a -> List (List a)
segments xs = singleton [] <>
  (filter (not <<< null) $ foldr _<>_ [] (tails <$> inits xs))

segmentsOfSize : Nat -> List a -> List (List a)
segmentsOfSize 0 _ = singleton []
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

zip : List a -> List b -> List (Pair a b)
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
  isSubsequenceOf xs ys =
      unsafePerform $ maybe False (const True) (foldlM g ys xs)
    where
      g : {{Partial}} -> List a -> a -> Maybe (List a)
      g s a = let s' = dropWhile (_/= a) s in
        case s' of \ where
          [] -> Nothing
          _ -> Just (tail s')

-------------------------------------------------------------------------------
-- Sublists
-------------------------------------------------------------------------------

stripPrefix : {{Eq a}} -> List a -> List a -> Maybe (List a)
stripPrefix xs ys =
  if isPrefixOf xs ys then Just (drop (length xs) ys) else Nothing

dropPrefix : {{Eq a}} -> List a -> List a -> List a
dropPrefix xs ys = maybe ys id (stripPrefix xs ys)

groupBy : (a -> a -> Bool) -> List a -> List (List a)
groupBy {a} eq xs = unsafePerform $ fromJust (petrol go (length xs) xs)
  where
    go : Fn (List a) (List (List a))
    go [] = pure []
    go (x :: xs) = do
      let (ys , zs) = span (eq x) xs
      res <- call zs
      pure $ (x :: ys) :: res

group : {{Eq a}} -> List a -> List (List a)
group = groupBy _==_

chunksOf : {{Partial}} -> Nat -> List a -> List (List a)
chunksOf 0 _ = undefined
chunksOf {a} n xs = fromJust (petrol go (length xs) xs)
  where
    go : Fn (List a) (List (List a))
    go [] = pure []
    go xs = do
      res <- call (drop n xs)
      pure $ take n xs :: res

breakOn : {{Eq a}} -> (needle haystack : List a) -> Pair (List a) (List a)
breakOn {a} needle haystack =
    unsafePerform $ fromJust (petrol go (length haystack) haystack)
  where
    go : Fn (List a) (Pair (List a) (List a))
    go haystack = do
      if isPrefixOf needle haystack
        then pure ([] , haystack)
        else case haystack of \ where
          [] -> pure ([] , [])
          (x :: xs) -> do
            res <- call xs
            pure $ lmap (x ::_) res

splitOn : {{Partial}} -> {{Eq a}} -> List a -> List a -> List (List a)
splitOn [] _ = undefined
splitOn {a} needle haystack =
    fromJust (petrol go (length haystack) haystack)
  where
    go : Fn (List a) (List (List a))
    go [] = pure $ singleton []
    go haystack = do
      let (l , r) = breakOn needle haystack
      res <- call $ drop (length needle) r
      pure $ l :: (if null r then [] else res)

split : (a -> Bool) -> List a -> List (List a)
split f [] = singleton []
split f (x :: xs) =
  if f x
    then [] :: split f xs
    else case split f xs of \ where
      [] -> singleton []
      (y :: ys) -> (x :: y) :: ys

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
-- Transformations
-------------------------------------------------------------------------------

intercalate : {{Monoid a}} -> a -> List a -> a
intercalate sep [] = neutral
intercalate sep (s :: []) = s
intercalate sep (s :: rest) = s <> sep <> intercalate sep rest

transpose : List (List a) -> List (List a)
transpose [] = []
transpose (heads :: tails) = zipCons heads (transpose tails)

sublists : List a -> List (List a)
sublists = filterA $ const (False :: True :: [])

sublistsN : Nat -> List a -> List (List a)
sublistsN 0 _ = singleton []
sublistsN _ [] = []
sublistsN (Suc n) (x :: xs) =
  map (x ::_) (sublistsN n xs) <> sublistsN (Suc n) xs

leaveOutOne : List a -> List (Pair a (List a))
leaveOutOne [] = []
leaveOutOne (x :: xs) = (x , xs) :: do
  (y , ys) <- leaveOutOne xs
  pure (y , x :: ys)

{-# TERMINATING #-}
permutations : List a -> List (List a)
permutations [] = singleton []
permutations xs = do
  (y , ys) <- leaveOutOne xs
  map (y ::_) (permutations ys)

-------------------------------------------------------------------------------
-- Sorting
-------------------------------------------------------------------------------

insertBy : (a -> a -> Ordering) -> a -> List a -> List a
insertBy cmp x [] = x :: []
insertBy cmp x ys@(y :: ys') =
  case cmp x y of \ where
    GT -> y :: insertBy cmp x ys'
    _ -> x :: ys

sortBy : (a -> a -> Ordering) -> List a -> List a
sortBy cmp [] = []
sortBy cmp (x :: xs) = insertBy cmp x (sortBy cmp xs)

module _ {{_ : Ord a}} where

  insert : a -> List a -> List a
  insert = insertBy compare

  sort : List a -> List a
  sort = sortBy compare

  sortOn : (b -> a) -> List b -> List b
  sortOn f = map snd <<< sortBy (comparing fst) <<< map (pair f id)

-------------------------------------------------------------------------------
-- Searching
-------------------------------------------------------------------------------

lookup : {{Eq a}} -> a -> List (Pair a b) -> Maybe b
lookup a [] = Nothing
lookup a ((a' , b) :: xs) = if a == a' then Just b else lookup a xs

-------------------------------------------------------------------------------
-- Misc.
-------------------------------------------------------------------------------

countElem : {{Eq a}} -> a -> List a -> Nat
countElem x = length <<< filter (x ==_)
