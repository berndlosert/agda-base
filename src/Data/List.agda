{-# OPTIONS --type-in-type #-}

module Data.List where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Data.Constraint.Nonempty
open import Data.Foldable
open import Data.Traversable

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a b c : Set
    f : Set -> Set

-------------------------------------------------------------------------------
-- Listlike
-------------------------------------------------------------------------------

record Listlike (s a : Set) : Set where
  infixr 5 _++_
  field
    {{Monofoldable-super}} : Monofoldable s a
    nil : s
    singleton : a -> s
    _++_ : s -> s -> s

  -- More Constructors

  cons : a -> s -> s
  cons x xs = singleton x ++ xs

  snoc : s -> a -> s
  snoc xs x = xs ++ singleton x

  fromList : List a -> s
  fromList [] = nil
  fromList (a :: as) = cons a (fromList as)

  fromMaybe : Maybe a -> s
  fromMaybe Nothing = nil
  fromMaybe (Just a) = singleton a

  replicate : Nat -> a -> s
  replicate n a = applyN (cons a) n nil

  -- Transformations

  reverse : s -> s
  reverse = foldl (flip cons) nil

  intersperse : a -> s -> s
  intersperse sep = flip foldr nil \ where
    a as -> if null as then singleton a else cons a (cons sep as)

  -- Extracting sublists

  takeWhile : (a -> Bool) -> s -> s
  takeWhile p = reverse <<< fromEither <<< flip foldlM nil \ where
    as a -> if p a then Right (cons a as) else Left as

  dropWhile : (a -> Bool) -> s -> s
  dropWhile p = reverse <<< flip foldl nil \ where
    as a -> if p a then as else (cons a as)

  take : Nat -> s -> s
  take n = reverse <<< snd <<< fromEither <<< flip foldlM (0 , nil) \ where
    (k , s) a -> if k < n then Right (Suc k , cons a s) else Left (Suc k , s)

  drop : Nat -> s -> s
  drop n = reverse <<< snd <<< flip foldl (0 , nil) \ where
    (k , as) a -> if k < n then (Suc k , as) else (Suc k , cons a as)

  span : (a -> Bool) -> s -> s * s
  span p xs = (takeWhile p xs , dropWhile p xs)

  break : (a -> Bool) -> s -> s * s
  break p = span (not <<< p)

  -- Indexed functions

  splitAt : Nat -> s -> s * s
  splitAt n as = (take n as , drop n as)

  at : Nat -> s -> Maybe a
  at n = leftToMaybe <<< flip foldlM 0 \
    k a -> if k == n then Left a else Right (Suc k)

  infixl 9 _!!_
  _!!_ : s -> Nat -> Maybe a
  _!!_ = flip at

  deleteAt : Nat -> s -> s
  deleteAt n = reverse <<< snd <<< flip foldl (0 , nil) \ where
    (k , as) a -> (Suc k , (if k == n then as else cons a as))

  modifyAt : Nat -> (a -> a) -> s -> s
  modifyAt n f = reverse <<< snd <<< flip foldl (0 , nil) \ where
    (k , as) a -> (Suc k , (if k == n then cons (f a) as else cons a as))

  setAt : Nat -> a -> s -> s
  setAt n a = modifyAt n (const a)

  insertAt : Nat -> a -> s -> s
  insertAt n a' = reverse <<< snd <<< flip foldl (0 , nil) \ where
    (k , as) a -> (Suc k , (if k == n then cons a' (cons a as) else cons a as))

  -- Searching with a predicate

  filter : (a -> Bool) -> s -> s
  filter p = foldr (\ a as -> if p a then cons a as else as) nil

  partition : (a -> Bool) -> s -> s * s
  partition p xs = (filter p xs , filter (not <<< p) xs)

open Listlike {{...}} public

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

instance
  Foldable-List : Foldable List
  Foldable-List .foldMap f = listrec mempty \ x _ y -> f x <> y

  Traversable-List : Traversable List
  Traversable-List .traverse f = listrec (pure []) \ where
    x _ ys -> (| _::_ (f x) ys |)

  Listlike-List : Listlike (List a) a
  Listlike-List .nil = []
  Listlike-List .singleton = [_]
  Listlike-List ._++_ = _<>_

-------------------------------------------------------------------------------
-- Destructors
-------------------------------------------------------------------------------

head : (xs : List a) {{_ : Nonempty xs}} -> a
head (a :: _) = a

tail : (xs : List a) {{_ : Nonempty xs}} -> List a
tail (_ :: as) = as

uncons : (xs : List a) {{_ : Nonempty xs}} -> a * List a
uncons (a :: as) = (a , as)

-------------------------------------------------------------------------------
-- Basic functions
-------------------------------------------------------------------------------

append : List a -> List a -> List a
append = _<>_

concat : List (List a) -> List a
concat = join

length : List a -> Nat
length = foldr (const Suc) 0

-------------------------------------------------------------------------------
-- Scans
-------------------------------------------------------------------------------

scanl : (b -> a -> b) -> b -> List a -> List b
scanl f b [] = [ b ]
scanl f b (a :: as) = b :: scanl f (f b a) as

scanr : (a -> b -> b) -> b -> List a -> List b
scanr f b [] = [ b ]
scanr f b (a :: as) = let as' = scanr f b as in
  f a (head as' {{believeMe}}) :: as'

-------------------------------------------------------------------------------
-- Sublists
-------------------------------------------------------------------------------

inits : List a -> List (List a)
inits = scanl snoc []

tails : List a -> List (List a)
tails = scanr cons []

stripPrefix : {{_ : Eq a}} -> List a -> List a -> Maybe (List a)
stripPrefix [] as = Just as
stripPrefix (x :: xs) (y :: ys) =
  if x == y then stripPrefix xs ys else Nothing
stripPrefix _ _ = Nothing

{-# TERMINATING #-}
groupBy : (a -> a -> Bool) -> List a -> List (List a)
groupBy _ [] = []
groupBy eq (x :: xs) = let (ys , zs) = span (eq x) xs in
  (x :: ys) :: groupBy eq zs

group : {{_ : Eq a}} -> List a -> List (List a)
group = groupBy _==_

-------------------------------------------------------------------------------
-- Index-based operations
-------------------------------------------------------------------------------

indexed : List a -> List (Nat * a)
indexed = reverse <<< flip foldl [] \ where
  [] a -> (0 , a) :: []
  xs@(h :: t) a' -> (Suc (fst h) , a') :: xs

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
  isPrefixOf [] _ = True
  isPrefixOf _ [] = False
  isPrefixOf (x :: xs) (y :: ys) = (x == y) && (isPrefixOf xs ys)

  isSuffixOf : List a -> List a -> Bool
  isSuffixOf xs ys = isPrefixOf (reverse xs) (reverse ys)

  isInfixOf : List a -> List a -> Bool
  isInfixOf [] _ = True
  isInfixOf _ [] = False
  isInfixOf as@(x :: xs) (y :: ys) =
    if x == y then isPrefixOf xs ys else isInfixOf as ys

  isSubsequenceOf : List a -> List a -> Bool
  isSubsequenceOf [] _ = True
  isSubsequenceOf _ [] = True
  isSubsequenceOf as@(x :: xs) (y :: ys) =
    if x == y then isSubsequenceOf xs ys else isSubsequenceOf as ys

-------------------------------------------------------------------------------
-- Filtering functions
-------------------------------------------------------------------------------

filterA : {{_ : Applicative f}} -> (a -> f Bool) -> List a -> f (List a)
filterA p = flip foldr (pure []) \ where
    a as -> (| if_then_else_ (p a) (| (a ::_) as |) as |)

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
