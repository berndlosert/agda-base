{-# OPTIONS --type-in-type #-}

module Data.List where

open import Prelude
  hiding (find)

private
  variable
    a b C : Set
    f : Set -> Set

--------------------------------------------------------------------------------
-- Destructors
--------------------------------------------------------------------------------

head : List a -> Maybe a
head [] = Nothing
head (a :: _) = Just a

tail : List a -> Maybe (List a)
tail [] = Nothing
tail (_ :: as) = Just as

uncons : List a -> Maybe (a * List a)
uncons [] = Nothing
uncons (a :: as) = Just (a , as)

--------------------------------------------------------------------------------
-- basic functions
--------------------------------------------------------------------------------

reverse : List a -> List a
reverse = foldl (flip _::_) []

length : List a -> Nat
length = foldr (const Suc) 0

--------------------------------------------------------------------------------
-- Sublists
--------------------------------------------------------------------------------

takeWhile : (a -> Bool) -> List a -> List a
takeWhile p = reverse ∘ untag ∘ flip foldlM [] λ where
  as a -> if p a then Right (a :: as) else Left as

dropWhile : (a -> Bool) -> List a -> List a
dropWhile p = reverse ∘ flip foldl [] λ where
  as a -> if p a then as else (a :: as)

take : Nat -> List a -> List a
take n = reverse ∘ snd ∘ untag ∘ flip foldlM (0 , []) λ where
  (k , s) a -> if k < n then Right (Suc k , cons a s) else Left (Suc k , s)

drop : Nat -> List a -> List a
drop n = reverse ∘ snd ∘ flip foldl (0 , []) λ where
  (k , as) a -> if k < n then (Suc k , as) else (Suc k , a :: as)

inits : List a -> List (List a)
inits = scanl snoc []

tails : List a -> List (List a)
tails = scanr cons []

span : (a -> Bool) -> List a -> List a * List a
span _ as@[] = (as , as)
span p as@(x :: xs) =
  if p x
  then (let (ys , zs) = span p xs in (x :: ys , zs))
  else ([] , xs)

break : (a -> Bool) -> List a -> List a * List a
break p [] = ([] , [])
break p as@(x :: xs) =
  if p x
  then ([] , as)
  else let (ys , zs) = break p xs in (x :: ys , zs)

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

{-# TERMINATING #-}
group : {{_ : Eq a}} -> List a -> List (List a)
group = groupBy _==_

--------------------------------------------------------------------------------
-- Index-based operations
--------------------------------------------------------------------------------

indexed : List a -> List (Nat * a)
indexed = reverse ∘ flip foldl [] λ where
  [] a -> (0 , a) :: []
  xs@(h :: t) a' -> (Suc (fst h) , a') :: xs

at : Nat -> List a -> Maybe a
at n = leftToMaybe ∘ flip foldlM 0 λ
  k a -> if k == n then Left a else Right (Suc k)

deleteAt : Nat -> List a -> List a
deleteAt n = reverse ∘ snd ∘ flip foldl (0 , nil) λ where
  (k , as) a -> (Suc k , if k == n then as else (a :: as))

modifyAt : Nat -> (a -> a) -> List a -> List a
modifyAt n f = reverse ∘ snd ∘ flip foldl (0 , nil) λ where
  (k , as) a -> (Suc k , if k == n then f a :: as else (a :: as))

setAt : Nat -> a -> List a -> List a
setAt n a = modifyAt n (const a)

insertAt : Nat -> a -> List a -> List a
insertAt n a' = reverse ∘ snd ∘ flip foldl (0 , nil) λ where
  (k , as) a -> (Suc k , if k == n then a' :: a :: as else (a :: as))

splitAt : Nat -> List a -> List a * List a
splitAt n as = (take n as , drop n as)

elemAt : Nat -> List a -> Maybe a
elemAt _ [] = Nothing
elemAt 0 (a :: _) = Just a
elemAt (Suc n) (_ :: as) = elemAt n as

--------------------------------------------------------------------------------
-- Zipping functions
--------------------------------------------------------------------------------

zipWith : (a -> b -> C) -> List a -> List b -> List C
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

--------------------------------------------------------------------------------
-- Predicates
--------------------------------------------------------------------------------

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

--------------------------------------------------------------------------------
-- Filtering functions
--------------------------------------------------------------------------------

filter : (a -> Bool) -> List a -> List a
filter p [] = []
filter p (a :: as) = if p a then a :: filter p as else filter p as

filterA : {{_ : Applicative f}} -> (a -> f Bool) -> List a -> f (List a)
filterA p = flip foldr (pure []) λ where
    a as -> (| if_then_else_ (p a) (| (a ::_) as |) as |)

partition : (a -> Bool) -> List a -> List a * List a
partition p = flip foldr ([] , []) λ where
  a (ts , fs) -> if p a then (a :: ts , fs) else (ts , a :: fs)

--------------------------------------------------------------------------------
-- Transformations
--------------------------------------------------------------------------------

intercalate : {{_ : Monoid a}} -> a -> List a -> a
intercalate sep [] = neutral
intercalate sep (s :: []) = s
intercalate sep (s :: rest) = s <> sep <> intercalate sep rest

intersperse : a -> List a -> List a
intersperse sep = flip foldr [] λ where
  a [] -> singleton a
  a as -> a :: sep :: as

transPose : List (List a) -> List (List a)
transPose [] = []
transPose (heads :: tails) = zipCons heads (transPose tails)

--------------------------------------------------------------------------------
-- Set-like operations
--------------------------------------------------------------------------------

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

--------------------------------------------------------------------------------
-- Sorting
--------------------------------------------------------------------------------

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
sortOn f = map snd ∘ sortBy (comparing fst) ∘ map (tuple f id)

--------------------------------------------------------------------------------
-- Searching
--------------------------------------------------------------------------------

lookup : {{_ : Eq a}} -> a -> List (a * b) -> Maybe b
lookup a [] = Nothing
lookup a ((a' , b) :: xs) = if a == a' then Just b else lookup a xs
