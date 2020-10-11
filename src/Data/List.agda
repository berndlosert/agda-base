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
    a b c s : Set
    f : Set -> Set

-------------------------------------------------------------------------------
-- Listlike
-------------------------------------------------------------------------------

record Listlike (s a : Set) : Set where
  infixr 5 _++_
  field
    {{Monofoldable-super}} : Monofoldable s a
    -- Basic constructors
    nil : s
    singleton : a -> s
    _++_ : s -> s -> s
    -- Basic destructors
    uncons : s -> Maybe (a * s)

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

  -- More destructors

  head : s -> Maybe a
  head = map fst <<< uncons

  tail : s -> Maybe s
  tail = map snd <<< uncons

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
  Listlike-List .uncons [] = Nothing
  Listlike-List .uncons (x :: xs) = Just (x , xs)

-------------------------------------------------------------------------------
-- Segments
-------------------------------------------------------------------------------

module _ {{_ : Listlike s a}} where

  inits : s -> List s
  inits = foldr (\ a ss -> [ nil ] ++ map (cons a) ss) [ nil ]

  tails : s -> List s
  tails = foldl (\ ss a -> map (flip snoc a) ss ++ [ nil ]) [ nil ]

  segments : s -> List s
  segments as =
    [ nil ] ++ (filter (not <<< null) $ foldr _++_ [] (tails <$> inits as))

  segmentsOfSize : Nat -> s -> List s
  segmentsOfSize 0 _ = [ nil ]
  segmentsOfSize n as =
    filter (\ s -> count s == n) $ foldr _++_ [] (tails <$> inits as)

-------------------------------------------------------------------------------
-- Scans
-------------------------------------------------------------------------------

module _ {{_ : Listlike s a}} where

  scanl : (b -> a -> b) -> b -> s -> List b
  scanl f b xs = foldl f b <$> inits xs

  scanr : (a -> b -> b) -> b -> s -> List b
  scanr f b xs = foldr f b <$> tails xs

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
    padding = replicate (count heads - count tails) []
    -- The tails that cannot be zipped because they have no corresponding
    -- head in heads.
    excess = snd (splitAt (count heads) tails)

-------------------------------------------------------------------------------
-- Predicates
-------------------------------------------------------------------------------

module _ {{_ : Listlike s a}} {{_ : Eq a}} where

  {-# TERMINATING #-}
  isPrefixOf : s -> s -> Bool
  isPrefixOf xs ys = case (uncons xs , uncons ys) of \ where
    (Nothing , _) -> True
    (_ , Nothing) -> False
    (Just (a , as) , Just (b , bs)) -> (a == b) && isPrefixOf as bs

  isSuffixOf : s -> s -> Bool
  isSuffixOf xs ys = isPrefixOf (reverse xs) (reverse ys)

  {-# TERMINATING #-}
  isInfixOf : s -> s -> Bool
  isInfixOf xs ys = case (uncons xs , uncons ys) of \ where
    (Nothing , _) -> True
    (_ , Nothing) -> False
    (Just (a , as) , Just (b , bs)) ->
      if a == b then isPrefixOf as bs else isInfixOf (cons a as) bs

  {-# TERMINATING #-}
  isSubsequenceOf : s -> s -> Bool
  isSubsequenceOf xs ys = case (uncons xs , uncons ys) of \ where
    (Nothing , _) -> True
    (_ , Nothing) -> False
    (Just (a , as) , Just (b , bs)) ->
      if a == b then isSubsequenceOf as bs else isSubsequenceOf (cons a as) bs

-------------------------------------------------------------------------------
-- Sublists
-------------------------------------------------------------------------------

module _ {{_ : Listlike s a}} where

  stripPrefix : {{_ : Eq a}} -> s -> s -> Maybe s
  stripPrefix xs ys =
    if isPrefixOf xs ys then Just (drop (count xs) ys) else Nothing

  {-# TERMINATING #-}
  groupBy : (a -> a -> Bool) -> s -> List s
  groupBy eq xs = case uncons xs of \ where
    Nothing -> []
    (Just (x , xs)) -> let (ys , zs) = span (eq x) xs in
      cons x ys :: groupBy eq zs

  group : {{_ : Eq a}} -> s -> List (s)
  group = groupBy _==_

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
