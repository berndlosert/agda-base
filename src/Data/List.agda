{-# OPTIONS --type-in-type #-}

module Data.List where

open import Data.List.Applicative public
open import Data.List.Alternative public
open import Data.List.Base public
open import Data.List.Foldable public
open import Data.List.Functor public
open import Data.List.Monad public
open import Data.List.Monoid public
open import Data.List.Semigroup public
open import Data.List.Traversable public

module List where

  open import Data.Bool
  open import Data.Eq
  open import Data.Function
  open import Data.Maybe
  open import Data.Nat
  open import Data.Pair

  private
    variable
      X Y Z : Set

  ------------------------------------------------------------------------------
  -- Overview
  ------------------------------------------------------------------------------

  -- Special constructors
  recons : Maybe (X * List X) -> List X
  fromMaybe : Maybe X -> List X
  replicate : Nat -> X -> List X
  til : Nat -> List Nat
  range : Nat -> Nat -> List Nat

  -- Special destructors
  tail : List X -> Maybe (List X)
  head : List X -> Maybe X
  uncons : List X -> Maybe (X * List X)

  -- Transformations
  reverse : List X -> List X
  transpose : List (List X) -> List (List X)

  -- Special folds
  concat : List (List X) -> List X
  concatMap : (X -> List Y) -> List X -> List Y
  cata : (Maybe (X * Y) -> Y) -> List X -> Y

  -- Searching lists
  filter : (X -> Bool) -> List X -> List X

  -- Extracting sublists
  take : Nat -> List X -> List X
  drop : Nat -> List X -> List X
  break : (X -> Bool) -> List X -> List X * List X
  splitAt : Nat -> List X -> List X * List X
  stripPrefix : {{_ : Eq X}} -> List X -> List X -> Maybe (List X)

  -- Predicates
  isPrefixOf : {{_ : Eq X}} -> List X -> List X -> Bool

  -- "By" operations
  deleteBy : (X -> X -> Bool) -> X -> List X -> List X
  unionBy : (X -> X -> Bool) -> List X -> List X -> List X
  nubBy : (X -> X -> Bool) -> List X -> List X

  -- Set-like operations
  delete : {{_ : Eq X}} -> X -> List X -> List X
  nub : {{_ : Eq X}} -> List X -> List X
  union : {{_ : Eq X}} -> List X -> List X -> List X

  -- Zipping
  zipWith : (X -> Y -> Z) -> List X -> List Y -> List Z
  zip : List X -> List Y -> List (X * Y)
  zipCons : List X -> List (List X) -> List (List X)

  -- Indexing lists
  elemAt : List X -> Nat -> Maybe X

  ------------------------------------------------------------------------------
  -- Details
  ------------------------------------------------------------------------------

  -- The join operation of the list monad is concat.
  concat = join

  -- Reversing a list is a natural transformation.
  reverse = foldl (flip _::_) []

  -- The filter function filters out elements of the list not satisfying
  -- the given predicate.
  filter p [] = []
  filter p (x :: xs) = if p x then x :: filter p xs else xs

  -- The break function finds the longest initial segment of a list that does
  -- not satisfy the given predicate and returns it paired with the remainder
  -- of the list.
  break p [] = Pair: [] []
  break p xs@(x :: xs') =
    if p x then Pair: [] xs
    else let Pair: ys zs = break p xs' in Pair: (x :: ys) zs

  -- The extend operation is concatMap.
  concatMap = extend

  -- Decompose a list into its head and tail if it isn't empty.
  uncons [] = nothing
  uncons (x :: xs) = just (Pair: x xs)

  -- The inverse of uncons. This proves that List X ~= Maybe (X * List X).
  recons nothing = []
  recons (just (Pair: x xs)) = x :: xs

  -- This proves that (List X , uncons) is an initial algebra. This is
  -- basically foldr in disguise.
  cata f [] = f nothing
  cata f (x :: xs) = f (just (Pair: x (cata f xs)))

  -- Returns the head of a nonempty list or nothing if it is empty.
  head [] = nothing
  head (x :: xs) = just x

  -- Returns the tail of a nonempty list or nothing if it is empty.
  tail [] = nothing
  tail (x :: xs) = just xs

  -- Takes two lists and returns true if the first list is a prefix of the
  -- second.
  isPrefixOf [] _ = true
  isPrefixOf _ [] = false
  isPrefixOf (x :: xs) (y :: ys) = (x == y) && (isPrefixOf xs ys)

  -- deleteBy eq x xs deletes the first item y in xs that satisfies eq x y.
  deleteBy _ _ [] = []
  deleteBy eq x (y :: ys) = if eq x y then ys else y :: deleteBy eq x ys

  -- Shorthand for deleteBy _==_.
  delete = deleteBy _==_

  -- Removes duplicate elements from a list where the duplicates are determined
  -- by the user-supplied equality predicate.
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

  -- Shorthand for nubBy _==_.
  nub = nubBy _==_

  -- Construct the union of two lists. Duplicates are removed according to the
  -- user-supplied equality predicate.
  unionBy eq xs ys = xs ++ foldl (flip (deleteBy eq)) (nubBy eq ys) ys

  -- Shorthand for unionBy _==_.
  union = unionBy _==_

  -- replicate n x is a list of length n with x the value of every element.
  replicate zero x = []
  replicate (suc n) x = x :: replicate n x

  -- take n, applied to a list xs, returns the prefix of xs of length n, or xs
  -- itself if n > length xs.
  take 0 _ = []
  take (suc n) [] = []
  take (suc n) (x :: xs) = x :: take n xs

  -- drop n xs returns the suffix of xs after the first n elements, or [] if
  -- n > length xs.
  drop 0 xs = xs
  drop (suc n) [] = []
  drop (suc n) (_ :: xs) = drop n xs

  -- Split a list into two pieces at the given index.
  splitAt n xs = Pair: (take n xs) (drop n xs)

  -- Zip two lists together with a function.
  zipWith f [] _ = []
  zipWith f _ [] = []
  zipWith f (x :: xs) (y :: ys) = f x y :: zipWith f xs ys

  -- Zip two lists into a list of pairs.
  zip = zipWith Pair:

  -- Zip together a list of heads and a list of tails.
  zipCons heads tails =
      (zipWith _::_ heads (tails ++ padding)) ++ excess
    where
      -- Extra tails that will be zipped with those heads that have no
      -- corresponding tail in tails.
      padding = replicate (size heads - size tails) []
      -- The tails that cannot be zipped because they have no corresponding
      -- head in heads.
      excess = snd (splitAt (size heads) tails)

  -- Transposes the elements of a list of lists (thought of as a matrix).
  transpose [] = []
  transpose (heads :: tails) = zipCons heads (transpose tails)

  -- til n returns a list of the first n natural numbers.
  til 0 = []
  til (suc n) = til n ++ pure n

  -- range m n produces a list of natural numbers from m to n.
  range m n = case compare m n of \ where
    GT -> []
    EQ -> pure n
    LT -> map (_+ m) $ til $ suc (n - m)

  -- The stripPrefix function drops the given prefix from a list. It returns
  -- nothing if the list did not start with the prefix given, or just the list
  -- after the prefix, if it does.
  stripPrefix [] ys = just ys
  stripPrefix (x :: xs) (y :: ys) =
    if x == y then stripPrefix xs ys else nothing
  stripPrefix _ _ = nothing

  -- This function returns an empty list when given nothing or the singleton
  -- list [ x ] when given just x.
  fromMaybe nothing = []
  fromMaybe (just x) = [ x ]

  -- elemAt xs n retrieves the (n - 1)th item in the list xs.
  elemAt [] _ = nothing
  elemAt (x :: xs) 0 = just x
  elemAt (x :: xs) (suc n) = elemAt xs n
