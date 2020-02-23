{-# OPTIONS --type-in-type #-}

module Data.List where

open import Prelude
  hiding (fromMaybe)

private
  variable
    X Y Z : Set

------------------------------------------------------------------------------
-- Special constructors
------------------------------------------------------------------------------

-- The inverse of uncons. This proves that List X ~= Maybe (X * List X).
recons : Maybe (X * List X) -> List X
recons nothing = []
recons (just (Pair: x xs)) = x :: xs

-- This function returns an empty list when given nothing or the singleton
-- list [ x ] when given just x.
fromMaybe : Maybe X -> List X
fromMaybe nothing = []
fromMaybe (just x) = [ x ]

-- replicate n x is a list of length n with x the value of every element.
replicate : Nat -> X -> List X
replicate zero x = []
replicate (suc n) x = x :: replicate n x

-- til n returns a list of the first n natural numbers.
til : Nat -> List Nat
til 0 = []
til (suc n) = til n ++ pure n

-- range m n produces a list of natural numbers from m to n.
range : Nat -> Nat -> List Nat
range m n = case compare m n of \ where
  GT -> []
  EQ -> pure n
  LT -> map (_+ m) $ til $ suc (n - m)

--------------------------------------------------------------------------------
-- Special destructors
--------------------------------------------------------------------------------

-- Returns the head of a nonempty list or nothing if it is empty.
head : List X -> Maybe X
head [] = nothing
head (x :: xs) = just x

-- Returns the tail of a nonempty list or nothing if it is empty.
tail : List X -> Maybe (List X)
tail [] = nothing
tail (x :: xs) = just xs

-- Decomposes a list into its head and tail if it isn't empty.
uncons : List X -> Maybe (X * List X)
uncons [] = nothing
uncons (x :: xs) = just (Pair: x xs)

--------------------------------------------------------------------------------
-- Special folds
--------------------------------------------------------------------------------

-- Flattens a list of lists into a list.
concat : List (List X) -> List X
concat = join

-- Map a function over all the elements of a container and concatenate the
-- resulting lists.
concatMap : (X -> List Y) -> List X -> List Y
concatMap = extend

-- and returns the conjunction of a container of Bools. For the result to be
-- true, the container must be finite; false, however, results from a false
-- value finitely far from the left end.
and : List Bool -> Bool
and = fold {{Monoid:All}}

-- or returns the disjunction of a container of Bools. For the result to be
-- false, the container must be finite; true, however, results from a true
-- value finitely far from the left end.
or : List Bool -> Bool
or = fold {{Monoid:Any}}

-- Determines whether any element of the structure satisfies the predicate.
any : forall {X} -> (X -> Bool) -> List X -> Bool
any f xs = or (map f xs)

-- Determines whether all elements of the structure satisfy the predicate.
all : forall {X} -> (X -> Bool) -> List X -> Bool
all f xs = and (map f xs)

--------------------------------------------------------------------------------
-- Searching lists
--------------------------------------------------------------------------------

-- The find function takes a predicate and a structure and returns the leftmost
-- element of the list matching the predicate, or nothing if there is no such
-- element.
find : (X -> Bool) -> List X -> Maybe X
find p xs = case filter p xs of \ where
  [] -> nothing
  (x :: _) -> just x

-- The partition function takes a predicate, a list and returns the pair of
-- lists of elements which do and do not satisfy the predicate.
partition : (X -> Bool) -> List X -> List X * List X
partition p xs = foldr (select p) (Pair: [] []) xs
  where
    select : (X -> Bool) -> X -> List X * List X -> List X * List X
    select p x (Pair: ts fs) with p x
    ... | true = Pair: (x :: ts) fs
    ... | false = Pair: ts (x :: fs)

--------------------------------------------------------------------------------
-- Extracting sublists
--------------------------------------------------------------------------------

-- take n, applied to a list xs, returns the prefix of xs of length n, or xs
-- itself if n > length xs.
take : Nat -> List X -> List X
take 0 _ = []
take (suc n) [] = []
take (suc n) (x :: xs) = x :: take n xs

-- drop n xs returns the suffix of xs after the first n elements, or [] if
-- n > length xs.
drop : Nat -> List X -> List X
drop 0 xs = xs
drop (suc n) [] = []
drop (suc n) (_ :: xs) = drop n xs

-- The break function finds the longest initial segment of a list that does
-- not satisfy the given predicate and returns it paired with the remainder
-- of the list.
break : (X -> Bool) -> List X -> List X * List X
break p [] = Pair: [] []
break p xs@(x :: xs') =
  if p x then Pair: [] xs
  else let Pair: ys zs = break p xs' in Pair: (x :: ys) zs

-- Splits a list into two pieces at the given index.
splitAt : Nat -> List X -> List X * List X
splitAt n xs = Pair: (take n xs) (drop n xs)

-- The stripPrefix function drops the given prefix from a list. It returns
-- nothing if the list did not start with the prefix given, or just the list
-- after the prefix, if it does.
stripPrefix : {{_ : Eq X}} -> List X -> List X -> Maybe (List X)
stripPrefix [] ys = just ys
stripPrefix (x :: xs) (y :: ys) =
  if x == y then stripPrefix xs ys else nothing
stripPrefix _ _ = nothing

-- The tails function returns all final segments of the argument, longest
-- first.
tails : forall {X} -> List X -> List (List X)
tails [] = [ [] ]
tails l@(x :: xs) = l :: tails xs

--------------------------------------------------------------------------------
-- "By" operations
--------------------------------------------------------------------------------

-- deleteBy eq x xs deletes the first item y in xs that satisfies eq x y.
deleteBy : (X -> X -> Bool) -> X -> List X -> List X
deleteBy _ _ [] = []
deleteBy eq x (y :: ys) = if eq x y then ys else y :: deleteBy eq x ys

-- Removes duplicate elements from a list where the duplicates are determined
-- by the user-supplied equality predicate.
nubBy : (X -> X -> Bool) -> List X -> List X
nubBy {X} eq l = nubBy' l []
  where
    elemBy : (X -> X -> Bool) -> X -> List X -> Bool
    elemBy _ _ [] = false
    elemBy eq y (x :: xs) = eq x y || elemBy eq y xs

    nubBy' : List X -> List X -> List X
    nubBy' [] _ = []
    nubBy' (y :: ys) xs =
      if elemBy eq y xs
      then nubBy' ys xs
      else y :: nubBy' ys (y :: xs)

-- Construct the union of two lists. Duplicates are removed according to the
-- user-supplied equality predicate.
unionBy : (X -> X -> Bool) -> List X -> List X -> List X
unionBy eq xs ys = xs ++ foldl (flip (deleteBy eq)) (nubBy eq ys) ys

--------------------------------------------------------------------------------
-- Set-like operations
--------------------------------------------------------------------------------

-- Deletes an element from a list.
delete : {{_ : Eq X}} -> X -> List X -> List X
delete = deleteBy _==_

-- The nub function removes duplicate elements from a list. In particular, it
-- keeps only the first occurrence of each element. (The name nub means
-- 'essence'.) It is a special case of nubBy, which allows the programmer to
-- supply their own equality test.
nub : {{_ : Eq X}} -> List X -> List X
nub = nubBy _==_

-- The union function returns the list union of the two lists. Duplicates, and
-- elements of the first list, are removed from the the second list, but if the
-- first list contains duplicates, so will the result. It is a special case of
-- unionBy, which allows the programmer to supply their own equality test.
union : {{_ : Eq X}} -> List X -> List X -> List X
union = unionBy _==_

--------------------------------------------------------------------------------
-- Zipping
--------------------------------------------------------------------------------

-- Zips two lists together with a function.
zipWith : (X -> Y -> Z) -> List X -> List Y -> List Z
zipWith f [] _ = []
zipWith f _ [] = []
zipWith f (x :: xs) (y :: ys) = f x y :: zipWith f xs ys

-- Zips two lists into a list of pairs.
zip : List X -> List Y -> List (X * Y)
zip = zipWith Pair:

-- Zips together a list of heads and a list of tails.
zipCons : List X -> List (List X) -> List (List X)
zipCons heads tails =
    (zipWith _::_ heads (tails ++ padding)) ++ excess
  where
    -- Extra tails that will be zipped with those heads that have no
    -- corresponding tail in tails.
    padding = replicate (length heads - length tails) []
    -- The tails that cannot be zipped because they have no corresponding
    -- head in heads.
    excess = snd (splitAt (length heads) tails)

--------------------------------------------------------------------------------
-- Transformations
--------------------------------------------------------------------------------

-- Reverses a list.
reverse : List X -> List X
reverse = foldl (flip _::_) []

-- Transposes the elements of a list of lists (thought of as a matrix).
transpose : List (List X) -> List (List X)
transpose [] = []
transpose (heads :: tails) = zipCons heads (transpose tails)

--------------------------------------------------------------------------------
-- Predicates
--------------------------------------------------------------------------------

-- Takes two lists and returns true if the first list is a prefix of the
-- second.
isPrefixOf : {{_ : Eq X}} -> List X -> List X -> Bool
isPrefixOf [] _ = true
isPrefixOf _ [] = false
isPrefixOf (x :: xs) (y :: ys) = (x == y) && (isPrefixOf xs ys)

-- The isSuffixOf function takes two lists and returns true iff the first list
-- is a suffix of the second.
isSuffixOf : {{_ : Eq X}} -> List X -> List X -> Bool
isSuffixOf xs ys = isPrefixOf (reverse xs) (reverse ys)

-- The isInfixOf function takes two lists and returns true iff the first list
-- is contained, wholly and intact, anywhere within the second.
isInfixOf : {{_ : Eq X}} -> List X -> List X -> Bool
isInfixOf xs ys = any (isPrefixOf xs) (tails ys)

------------------------------------------------------------------------------
-- Indexing lists
------------------------------------------------------------------------------

-- elemAt xs n retrieves the (n - 1)th item in the list xs.
elemAt : List X -> Nat -> Maybe X
elemAt [] _ = nothing
elemAt (x :: xs) 0 = just x
elemAt (x :: xs) (suc n) = elemAt xs n
