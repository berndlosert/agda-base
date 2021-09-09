{-# OPTIONS --type-in-type #-}

module Data.List1 where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Control.Monad.Free.General
open import Data.Monoid.Endo
open import Data.Filterable
open import Data.Foldable
open import Data.List as List using ()
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

singleton : a -> List1 a
singleton = _:| []

cons : a -> List1 a -> List1 a
cons x (y :| ys) = x :| y :: ys

snoc : List1 a -> a -> List1 a
snoc xs x = xs <> singleton x

fromList : List a -> Maybe (List1 a)
fromList [] = Nothing
fromList (x :: xs) = Just (x :| xs)

iterateN : Nat1 -> (a -> a) -> a -> List1 a
iterateN (suc 0) f x = singleton x
iterateN (suc n) f x = f x :| List.iterateN n f x

replicate : Nat1 -> a -> List1 a
replicate n = iterateN n id

replicateA : {{Applicative f}} -> Nat1 -> f a -> f (List1 a)
replicateA {f} {a} n0 fa = loop n0
  where
    loop : Nat1 -> f (List1 a)
    loop (suc 0) = map singleton fa
    loop (suc (suc n)) = (| cons fa (loop (suc n)) |)

-------------------------------------------------------------------------------
-- Destructors
-------------------------------------------------------------------------------

head : List1 a -> a
head (x :| _) = x

tail : List1 a -> List a
tail (_ :| xs) = xs

uncons : List1 a -> Pair a (List a)
uncons (x :| xs) = (x , xs)

unsnoc : List1 a -> Pair (List a) a
unsnoc (x :| xs) = fromMaybe ([] , x) (List.unsnoc (x :: xs))

init : List1 a -> List a
init (x :| xs) = maybe [] (x ::_) (List.init xs)

-------------------------------------------------------------------------------
-- Transformations
-------------------------------------------------------------------------------

reverse : List1 a -> List1 a
reverse (x :| xs) =
  case fromList (List.reverse xs) of \ where
    Nothing -> x :| []
    (Just xs') -> snoc xs' x

intersperse : a -> List1 a -> List1 a
intersperse sep (x :| []) = x :| []
intersperse sep (x :| xs) = x :| sep :: List.intersperse sep xs

-------------------------------------------------------------------------------
-- Extracting sublists
-------------------------------------------------------------------------------

takeWhile : (a -> Bool) -> List1 a -> List a
takeWhile p (x :| xs) = List.takeWhile p (x :: xs)

dropWhile : (a -> Bool) -> List1 a -> List a
dropWhile p (x :| xs) = List.dropWhile p (x :: xs)

take : Nat -> List1 a -> List a
take n (x :| xs) = List.take n (x :: xs)

drop : Nat -> List1 a -> List a
drop n (x :| xs) = List.drop n (x :: xs)

span : (a -> Bool) -> List1 a -> Pair (List a) (List a)
span p (x :| xs) = List.span p (x :: xs)

break : (a -> Bool) -> List1 a -> Pair (List a) (List a)
break p (x :| xs) = List.break p (x :: xs)

-------------------------------------------------------------------------------
-- Indexed functions
-------------------------------------------------------------------------------

indexed : List1 a -> List1 (Pair Nat a)
indexed (x :| xs) = (0 , x) :| map (lmap suc) (List.indexed xs)

splitAt : Nat -> List1 a -> Pair (List a) (List a)
splitAt n xs = (take n xs , drop n xs)

at : Nat -> List1 a -> Maybe a
at 0 (x :| _) = Just x
at (suc n) (x :| []) = Nothing
at (suc n) (x :| (y :: ys)) = at n (y :| ys)

updateAt : Nat -> (a -> Maybe a) -> List1 a -> List a
updateAt 0 f (x :| xs) = maybe xs (_:: xs) (f x)
updateAt (suc n) f (x :| xs) = x :: List.updateAt n f xs

deleteAt : Nat -> List1 a -> List a
deleteAt n = updateAt n (const Nothing)

modifyAt : Nat -> (a -> a) -> List1 a -> List1 a
modifyAt 0 f (x :| xs) = f x :| xs
modifyAt (suc n) f (x :| xs) = x :| List.modifyAt n f xs

setAt : Nat -> a -> List1 a -> List1 a
setAt n x = modifyAt n (const x)

insertAt : Nat -> a -> List1 a -> List1 a
insertAt 0 x (y :| ys) = x :| y :: ys
insertAt (suc n) x (y :| ys) = y :| List.insertAt n x ys

-------------------------------------------------------------------------------
-- Segments
-------------------------------------------------------------------------------

inits : List1 a -> List1 (List1 a)
inits (x :| xs) = (x :| []) :| map (x :|_) (List.inits xs)

tails : List1 a -> List1 (List1 a)
tails (x :| []) = (x :| []) :| []
tails (x :| y :: ys) = (x :| y :: ys) :| map (y :|_) (List.tails ys)

segments : List1 a -> List1 (List1 a)
segments (x :| []) = (x :| []) :| []
segments (x :| y :: ys) = foldr _<>_ ((x :| []) :| []) (tails <$> inits (y :| ys))
--
--segmentsOfSize : Nat -> List a -> List (List a)
--segmentsOfSize 0 _ = singleton []
--segmentsOfSize n xs =
--  filter (\ ys -> length ys == n) $ foldr _<>_ [] (tails <$> inits xs)
--
---------------------------------------------------------------------------------
---- Scans
---------------------------------------------------------------------------------
--
--scanl : (b -> a -> b) -> b -> List a -> List b
--scanl f b xs = foldl f b <$> inits xs
--
--scanr : (a -> b -> b) -> b -> List a -> List b
--scanr f b xs = foldr f b <$> tails xs
--
---------------------------------------------------------------------------------
---- Zipping functions
---------------------------------------------------------------------------------
--
--zipWith : (a -> b -> c) -> List a -> List b -> List c
--zipWith f [] _ = []
--zipWith f _ [] = []
--zipWith f (x :: xs) (y :: ys) = f x y :: zipWith f xs ys
--
--zip : List a -> List b -> List (Pair a b)
--zip = zipWith _,_
--
---- Zips together a list of heads and a list of tails.
--zipCons : List a -> List (List a) -> List (List a)
--zipCons heads tails =
--    (zipWith _::_ heads (tails <> padding)) <> excess
--  where
--    -- Extra tails that will be zipped with those heads that have no
--    -- corresponding tail in tails.
--    padding = replicate (monus (length heads) (length tails)) []
--    -- The tails that cannot be zipped because they have no corresponding
--    -- head in heads.
--    excess = snd (splitAt (length heads) tails)
--
---------------------------------------------------------------------------------
---- Predicates
---------------------------------------------------------------------------------
--
--module _ {{_ : Eq a}} where
--
--  isPrefixOf : List a -> List a -> Bool
--  isPrefixOf xs ys = take (length xs) ys == xs
--
--  isSuffixOf : List a -> List a -> Bool
--  isSuffixOf xs ys = isPrefixOf xs (drop (length xs) ys)
--
--  isInfixOf : List a -> List a -> Bool
--  isInfixOf xs ys = maybe false (const true) $
--    find (_== xs) (segmentsOfSize (length xs) ys)
--
--  isSubsequenceOf : List a -> List a -> Bool
--  isSubsequenceOf xs ys =
--      maybe false (const true) (foldlM g ys xs)
--    where
--      g : List a -> a -> Maybe (List a)
--      g s a = let s' = dropWhile (_/= a) s in
--        case s' of \ where
--          [] -> Nothing
--          _ -> tail s'
--
---------------------------------------------------------------------------------
---- Sorting
---------------------------------------------------------------------------------
--
--insertBy : (a -> a -> Ordering) -> a -> List a -> List a
--insertBy cmp x [] = x :: []
--insertBy cmp x ys@(y :: ys') =
--  case cmp x y of \ where
--    GT -> y :: insertBy cmp x ys'
--    _ -> x :: ys
--
--sortBy : (a -> a -> Ordering) -> List a -> List a
--sortBy cmp [] = []
--sortBy cmp (x :: xs) = insertBy cmp x (sortBy cmp xs)
--
--module _ {{_ : Ord a}} where
--
--  insert : a -> List a -> List a
--  insert = insertBy compare
--
--  sort : List a -> List a
--  sort = sortBy compare
--
--  sortOn : (b -> a) -> List b -> List b
--  sortOn f = map snd <<< sortBy (comparing fst) <<< map (pair f id)
--
---------------------------------------------------------------------------------
---- Sublists
---------------------------------------------------------------------------------
--
--stripPrefix : {{Eq a}} -> List a -> List a -> Maybe (List a)
--stripPrefix xs ys =
--  if isPrefixOf xs ys then Just (drop (length xs) ys) else Nothing
--
--dropPrefix : {{Eq a}} -> List a -> List a -> List a
--dropPrefix xs ys = maybe ys id (stripPrefix xs ys)
--
--groupBy : (a -> a -> Bool) -> List a -> List (List a)
--groupBy {a} eq xs = unsafePerform $ fromJust (petrol go (length xs) xs)
--  where
--    go : Fn (List a) (List (List a))
--    go [] = pure []
--    go (x :: xs) = do
--      let (ys , zs) = span (eq x) xs
--      res <- call zs
--      pure $ (x :: ys) :: res
--
--group : {{Eq a}} -> List a -> List (List a)
--group = groupBy _==_
--
--groupOn : {{Ord b}} -> (a -> b) -> List a -> List (List a)
--groupOn f = groupBy (equating f) <<< sortBy (comparing f)
--
--chunksOf : {{Partial}} -> Nat -> List a -> List (List a)
--chunksOf 0 _ = undefined
--chunksOf {a} n xs = fromJust (petrol go (length xs) xs)
--  where
--    go : Fn (List a) (List (List a))
--    go [] = pure []
--    go xs = do
--      res <- call (drop n xs)
--      pure $ take n xs :: res
--
--breakOn : {{Eq a}} -> (needle haystack : List a) -> Pair (List a) (List a)
--breakOn {a} needle haystack =
--    unsafePerform $ fromJust (petrol go (length haystack) haystack)
--  where
--    go : Fn (List a) (Pair (List a) (List a))
--    go haystack = do
--      if isPrefixOf needle haystack
--        then pure ([] , haystack)
--        else case haystack of \ where
--          [] -> pure ([] , [])
--          (x :: xs) -> do
--            res <- call xs
--            pure $ lmap (x ::_) res
--
--splitOn : {{Partial}} -> {{Eq a}} -> List a -> List a -> List (List a)
--splitOn [] _ = undefined
--splitOn {a} needle haystack =
--    fromJust (petrol go (length haystack) haystack)
--  where
--    go : Fn (List a) (List (List a))
--    go [] = pure $ singleton []
--    go haystack = do
--      let (l , r) = breakOn needle haystack
--      res <- call $ drop (length needle) r
--      pure $ l :: (if null r then [] else res)
--
--split : (a -> Bool) -> List a -> List (List a)
--split f [] = singleton []
--split f (x :: xs) =
--  if f x
--    then [] :: split f xs
--    else case split f xs of \ where
--      [] -> singleton []
--      (y :: ys) -> (x :: y) :: ys
--
---------------------------------------------------------------------------------
---- Set-like operations
---------------------------------------------------------------------------------
--
--deleteBy : (a -> a -> Bool) -> a -> List a -> List a
--deleteBy _ _ [] = []
--deleteBy eq x (y :: ys) = if eq x y then ys else (y :: deleteBy eq x ys)
--
--nubBy : (a -> a -> Bool) -> List a -> List a
--nubBy {a} eq l = nubBy' l []
--  where
--    elemBy : (a -> a -> Bool) -> a -> List a -> Bool
--    elemBy _ _ [] = false
--    elemBy eq y (x :: xs) = eq x y || elemBy eq y xs
--
--    nubBy' : List a -> List a -> List a
--    nubBy' [] _ = []
--    nubBy' (y :: ys) xs =
--      if elemBy eq y xs
--      then nubBy' ys xs
--      else (y :: nubBy' ys (y :: xs))
--
--unionBy : (a -> a -> Bool) -> List a -> List a -> List a
--unionBy eq xs ys = xs <> foldl (flip (deleteBy eq)) (nubBy eq ys) ys
--
--module _ {{_ : Eq a}} where
--
--  delete : a -> List a -> List a
--  delete = deleteBy _==_
--
--  nub : List a -> List a
--  nub = nubBy _==_
--
--  union : List a -> List a -> List a
--  union = unionBy _==_
--
---------------------------------------------------------------------------------
---- Transformations
---------------------------------------------------------------------------------
--
--intercalate : {{Monoid a}} -> a -> List a -> a
--intercalate sep [] = neutral
--intercalate sep (s :: []) = s
--intercalate sep (s :: rest) = s <> sep <> intercalate sep rest
--
--transpose : List (List a) -> List (List a)
--transpose [] = []
--transpose (heads :: tails) = zipCons heads (transpose tails)
--
--sublists : List a -> List (List a)
--sublists = filterA $ const (false :: true :: [])
--
--sublistsN : Nat -> List a -> List (List a)
--sublistsN 0 _ = singleton []
--sublistsN _ [] = []
--sublistsN (suc n) (x :: xs) =
--  map (x ::_) (sublistsN n xs) <> sublistsN (suc n) xs
--
--leaveOutOne : List a -> List (Pair a (List a))
--leaveOutOne [] = []
--leaveOutOne (x :: xs) = (x , xs) :: do
--  (y , ys) <- leaveOutOne xs
--  pure (y , x :: ys)
--
--{-# TERMINATING #-}
--permutations : List a -> List (List a)
--permutations [] = singleton []
--permutations xs = do
--  (y , ys) <- leaveOutOne xs
--  map (y ::_) (permutations ys)
--
---------------------------------------------------------------------------------
---- Searching
---------------------------------------------------------------------------------
--
--lookup : {{Eq a}} -> a -> List (Pair a b) -> Maybe b
--lookup a [] = Nothing
--lookup a ((a' , b) :: xs) = if a == a' then Just b else lookup a xs
--
---------------------------------------------------------------------------------
---- Misc.
---------------------------------------------------------------------------------
--
--countElem : {{Eq a}} -> a -> List a -> Nat
--countElem x = length <<< filter (x ==_)
