module Data.List where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Data.Filterable
open import Data.Foldable
open import Data.Monoid.Endo
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
iterateN (suc n) f x = f x :: iterateN n f x

replicate : Nat -> a -> List a
replicate n = iterateN n id

replicateA : {{Applicative f}} -> Nat -> f a -> f (List a)
replicateA {f} {a} n0 fa = loop n0
  where
    loop : Nat -> f (List a)
    loop 0 = pure []
    loop (suc n) = (| fa :: loop n |)

build : (forall {b} -> (a -> b -> b) -> b -> b) -> List a
build g = g _::_ []

-------------------------------------------------------------------------------
-- Destructors
-------------------------------------------------------------------------------

head : List a -> Maybe a
head [] = nothing
head (x :: _) = just x

tail : List a -> Maybe (List a)
tail [] = nothing
tail (_ :: xs) = just xs

uncons : List a -> Maybe (Pair a (List a))
uncons [] = nothing
uncons (x :: xs) = just (x , xs)

unsnoc : List a -> Maybe (Pair (List a) a)
unsnoc [] = nothing
unsnoc xs = foldr go nothing xs
  where
    go : a -> Maybe (Pair (List a) a) -> Maybe (Pair (List a) a)
    go x nothing = just ([] , x)
    go x (just (xs , e)) = just (x :: xs , e)

init : List a -> Maybe (List a)
init [] = nothing
init (x :: []) = just []
init (x :: xs@(_ :: _)) = (| pure x :: init xs |)

-------------------------------------------------------------------------------
-- Transformations
-------------------------------------------------------------------------------

reverse : List a -> List a
reverse = foldl' (flip cons) []

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
take (suc n) (x :: xs) = x :: take n xs

drop : Nat -> List a -> List a
drop _ [] = []
drop 0 xs = xs
drop (suc n) (x :: xs) = drop n xs

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
    go n (y :: ys) = (n , y) :: go (suc n) ys

splitAt : Nat -> List a -> Pair (List a) (List a)
splitAt n xs = (take n xs , drop n xs)

at : Nat -> List a -> Maybe a
at _ [] = nothing
at 0 (x :: _) = just x
at (suc n) (_ :: xs) = at n xs

updateAt : Nat -> (a -> Maybe a) -> List a -> List a
updateAt 0 f (x :: xs) = maybe xs (_:: xs) (f x)
updateAt (suc n) f (x :: xs) = x :: updateAt n f xs
updateAt _ _ [] = []

deleteAt : Nat -> List a -> List a
deleteAt n = updateAt n (const nothing)

modifyAt : Nat -> (a -> a) -> List a -> List a
modifyAt n f = updateAt n (f >>> just)

setAt : Nat -> a -> List a -> List a
setAt n x = modifyAt n (const x)

insertAt : Nat -> a -> List a -> List a
insertAt 0 x (y :: ys) = x :: y :: ys
insertAt (suc n) x (y :: ys) = y :: insertAt n x ys
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

scanl' : (b -> a -> b) -> b -> List a -> List b
scanl' f b xs = foldl' f b <$> inits xs

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

unzip : List (Pair a b) -> Pair (List a) (List b)
unzip [] = ([] , [])
unzip ((x , y) :: ps) = case unzip ps of \ where
  (xs , ys) -> (x :: xs , y :: ys)

-------------------------------------------------------------------------------
-- Predicates
-------------------------------------------------------------------------------

module _ {{_ : Eq a}} where

  isPrefixOf : List a -> List a -> Bool
  isPrefixOf xs ys = take (length xs) ys == xs

  isSuffixOf : List a -> List a -> Bool
  isSuffixOf xs ys = isPrefixOf xs (drop (length xs) ys)

  isInfixOf : List a -> List a -> Bool
  isInfixOf xs ys = maybe false (const true) $
    find (_== xs) (segmentsOfSize (length xs) ys)

  isSubsequenceOf : List a -> List a -> Bool
  isSubsequenceOf xs ys =
      maybe false (const true) (foldlM g ys xs)
    where
      g : List a -> a -> Maybe (List a)
      g s a = case dropWhile (_/= a) s of \ where
        [] -> nothing
        (x :: xs) -> just xs

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
  sortOn f = map snd
    <<< sortBy (compare on fst)
    <<< map (\ x -> let y = f x in y seq (y , x))

-------------------------------------------------------------------------------
-- Sublists
-------------------------------------------------------------------------------

stripPrefix : {{Eq a}} -> List a -> List a -> Maybe (List a)
stripPrefix xs ys =
  if isPrefixOf xs ys then just (drop (length xs) ys) else nothing

dropPrefix : {{Eq a}} -> List a -> List a -> List a
dropPrefix xs ys = maybe ys id (stripPrefix xs ys)

groupBy : (a -> a -> Bool) -> List a -> List (List a)
groupBy eq [] = []
groupBy eq (x :: xs) =
  let (ys , zs) = span (eq x) xs
  in (x :: ys) :: groupBy eq zs

group : {{Eq a}} -> List a -> List (List a)
group = groupBy _==_

groupOn : {{Ord b}} -> (a -> b) -> List a -> List (List a)
groupOn f = groupBy (_==_ on f) <<< sortBy (compare on f)

chunksOf : Nat -> List a -> List (List a)
chunksOf n [] = []
chunksOf n xs = take n xs :: chunksOf n (drop n xs)

breakOn : {{Eq a}} -> (needle haystack : List a) -> Pair (List a) (List a)
breakOn needle haystack =
  if isPrefixOf needle haystack
    then ([] , haystack)
    else case haystack of \ where
      [] -> ([] , [])
      (x :: xs) -> case breakOn needle xs of \ where
        (ys , zs) -> (x :: ys , zs)

splitOn : {{Eq a}} -> List a -> List a -> List (List a)
splitOn needle [] = singleton []
splitOn needle haystack =
  let (l , r) = breakOn needle haystack
  in l :: (if null r then [] else splitOn needle (drop (length needle) r))

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
    elemBy _ _ [] = false
    elemBy eq y (x :: xs) = eq x y || elemBy eq y xs

    nubBy' : List a -> List a -> List a
    nubBy' [] _ = []
    nubBy' (y :: ys) xs =
      if elemBy eq y xs
      then nubBy' ys xs
      else (y :: nubBy' ys (y :: xs))

unionBy : (a -> a -> Bool) -> List a -> List a -> List a
unionBy eq xs ys = xs <> foldl' (flip (deleteBy eq)) (nubBy eq ys) ys

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
intercalate sep [] = mempty
intercalate sep (s :: []) = s
intercalate sep (s :: rest) = s <> sep <> intercalate sep rest

transpose : List (List a) -> List (List a)
transpose [] = []
transpose (heads :: tails) = zipCons heads (transpose tails)

sublists : List a -> List (List a)
sublists = filterA $ const (false :: true :: [])

sublistsN : Nat -> List a -> List (List a)
sublistsN 0 _ = singleton []
sublistsN _ [] = []
sublistsN (suc n) (x :: xs) =
  map (x ::_) (sublistsN n xs) <> sublistsN (suc n) xs

leaveOutOne : List a -> List (Pair a (List a))
leaveOutOne [] = []
leaveOutOne (x :: xs) = (x , xs) :: do
  (y , ys) <- leaveOutOne xs
  pure (y , x :: ys)

permutations : List a -> List (List a)
permutations [] = singleton []
permutations xs = do
  (y , ys) <- leaveOutOne xs
  map (y ::_) (permutations ys)

-------------------------------------------------------------------------------
-- Searching
-------------------------------------------------------------------------------

lookup : {{Eq a}} -> a -> List (Pair a b) -> Maybe b
lookup a [] = nothing
lookup a ((a' , b) :: xs) = if a == a' then just b else lookup a xs

-------------------------------------------------------------------------------
-- Misc.
-------------------------------------------------------------------------------

countElem : {{Eq a}} -> a -> List a -> Nat
countElem x = length <<< filter (x ==_)
