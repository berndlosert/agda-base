{-# OPTIONS --type-in-type #-}

module Data.List.Api where

open import Data.List.Base

-- List is foldable.

open import Data.Foldable public
open import Data.Monoid

instance
  Foldable:List : Foldable List
  Foldable:List .lift = [_]
  Foldable:List .foldMap f [] = mempty
  Foldable:List .foldMap f (x :: xs) = f x <> foldMap f xs

-- List is a monad.

open import Control.Category
open import Control.Monad
open import Data.Functor

instance
  Monad:List : Monad Sets List
  Monad:List .return = [_]
  Monad:List .extend k [] = [] 
  Monad:List .extend k (x :: xs) = k x ++ extend k xs

-- The join operation of the list monad is concat.

concat : forall {X} -> List (List X) -> List X 
concat = join

-- List is traversable.

open import Control.Applicative
open import Data.Traversable

instance
  Traversable:List : Traversable List
  Traversable:List .sequence {F} {X} = foldr cons (pure [])
    where
      cons : F X -> F (List X) -> F (List X)
      cons x xs = (| _::_ x xs |)

-- Reversing a list is a natural transformation.

open import Data.Function

reverse : List ~> List
reverse = foldl (flip _::_) []

-- The filter function filters out elements of the list not satisfying
-- the given predicate.

open import Data.Bool

filter : forall {X} -> (X -> Bool) -> List X -> List X
filter p [] = []
filter p (x :: xs) = if p x then x :: filter p xs else xs

-- The break function finds the longest initial segment of a list that does
-- not satisfy the given predicate and returns it paired with the remainder
-- of the list.

open import Data.Product

break : forall {X} -> (X -> Bool) -> List X -> List X * List X
break p [] = ([] , [])
break p xs@(x :: xs') =
  if p x then ([] , xs)
  else let (ys , zs) = break p xs' in (x :: ys , zs)

-- The extend operation is concatMap.

concatMap : forall {X Y} -> (X -> List Y) -> List X -> List Y
concatMap = extend

-- There are two known applicative instances of List: the one derived from
-- the monad instance and the ZipList one.

open import Control.Applicative
Applicative:List : Applicative List
Applicative:List = Idiom: ap return

Applicative:ZipList : Applicative List
Applicative:ZipList = Applicative: zipList [_]
  where
    zipList : {X Y : Set} -> List X * List Y -> List (X * Y)
    zipList ([] , _) = []
    zipList (_ , []) = []
    zipList (x :: xs , y :: ys) = (x , y) :: zipList (xs , ys)

-- A generalization of zip.

zipWith : forall {X Y Z} -> (X -> Y -> Z) -> List X -> List Y -> List Z
zipWith f [] _ = []
zipWith f _ [] = []
zipWith f (x :: xs) (y :: ys) = f x y :: zipWith f xs ys

open import Data.Maybe

-- Decompose a list into its head and tail if it isn't empty.

uncons : forall {X} -> List X -> Maybe (X * List X)
uncons [] = nothing
uncons (x :: xs) = just (x , xs)

-- The inverse of uncons. This proves that List X ~= Maybe (X * List X).

recons : forall {X} -> Maybe (X * List X) -> List X
recons nothing = []
recons (just (x , xs)) = x :: xs

-- This proves that (List X , uncons) is an initial algebra. This is basically
-- foldr in disguise.

cata : forall {X Y} -> (Maybe (X * Y) -> Y) -> List X -> Y
cata f [] = f nothing
cata f (x :: xs) = f (just (x , cata f xs))

-- Returns the head of a nonempty list.

head : forall {X} (xs : List X) -> {_ : Nonempty xs} -> X
head (x :: xs) = x

-- Maybe version of head.

head? : forall {X} -> List X -> Maybe X
head? [] = nothing
head? (x :: xs) = just x

-- Returns the tail of a nonempty list.

tail : forall {X} (xs : List X) -> {_ : Nonempty xs} -> List X
tail (x :: xs) = xs

-- Maybe version of tail.

tail? : forall {X} -> List X -> Maybe (List X)
tail? [] = nothing
tail? (x :: xs) = just xs

-- Takes two lists and returns true if the first list is a prefix of the
-- second.

open import Data.Eq

isPrefixOf : forall {X} {{_ : Eq X}} -> List X -> List X -> Bool
isPrefixOf [] _ = true
isPrefixOf _ [] = false
isPrefixOf (x :: xs) (y :: ys) = (x == y) && (isPrefixOf xs ys)

-- deleteBy eq x xs deletes the first item y in xs that satisfies eq x y.

deleteBy : forall {X} -> (X -> X -> Bool) -> X -> List X -> List X
deleteBy _ _ [] = []
deleteBy eq x (y :: ys) = if eq x y then ys else y :: deleteBy eq x ys

-- Shorthand for deleteBy _==_.

delete : forall {X} {{_ : Eq X}} -> X -> List X -> List X
delete = deleteBy _==_

-- Removes duplicate elements from a list where the duplicates are determined
-- by the user-supplied equality predicate.

nubBy : forall {X} -> (X -> X -> Bool) -> List X -> List X
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

nub : forall {X} {{_ : Eq X}} -> List X -> List X
nub = nubBy _==_

-- Construct the union of two lists. Duplicates are removed according to the
-- user-supplied equality predicate.

unionBy : forall {X} -> (X -> X -> Bool) -> List X -> List X -> List X
unionBy eq xs ys = xs ++ foldl (flip (deleteBy eq)) (nubBy eq ys) ys

-- Shorthand for unionBy _==_.

union : forall {X} {{_ : Eq X}} -> List X -> List X -> List X
union = unionBy _==_

-- replicate n x is a list of length n with x the value of every element.

open import Data.Nat.Base

replicate : forall {X} -> Nat -> X -> List X
replicate 0 x = []
replicate (suc n) x = x :: replicate n x
