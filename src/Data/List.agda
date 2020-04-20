{-# OPTIONS --type-in-type #-}

module Data.List where

open import Prelude

private variable A B C : Set

--------------------------------------------------------------------------------
-- Destructors
--------------------------------------------------------------------------------

head : List A -> Maybe A
head [] = nothing
head (a :: _) = just a

tail : List A -> Maybe (List A)
tail [] = nothing
tail (_ :: as) = just as

uncons : List A -> Maybe (A * List A)
uncons [] = nothing
uncons (a :: as) = just (a , as)

--------------------------------------------------------------------------------
-- Basic functions
--------------------------------------------------------------------------------

reverse : List A -> List A
reverse = foldl (flip _::_) []

length : List A -> Nat
length = foldr (const suc) 0

--------------------------------------------------------------------------------
-- Generators
--------------------------------------------------------------------------------

til : Nat -> List Nat
til 0 = []
til (suc n) = til n ++ singleton n

replicate : Nat -> A -> List A
replicate n a = applyN (a ::_) n []

range : Nat -> Nat -> List Nat
range m n with compare m n
... | GT = []
... | EQ = singleton n
... | LT = map (_+ m) $ til $ suc (monus n m)

--------------------------------------------------------------------------------
-- Functions producing sublists
--------------------------------------------------------------------------------

takeWhile : (A -> Bool) -> List A -> List A
takeWhile p = reverse <<< untag <<< flip foldlM [] \ where
  as a -> if p a then right (a :: as) else left as

dropWhile : (A -> Bool) -> List A -> List A
dropWhile p = reverse <<< flip foldl [] \ where
  as a -> if p a then as else (a :: as)

take : Nat -> List A -> List A
take n = reverse <<< snd <<< untag <<< flip foldlM (0 , []) \ where
  (k , s) a -> if k < n then right (suc k , cons a s) else left (suc k , s)

drop : Nat -> List A -> List A
drop n = reverse <<< snd <<< flip foldl (0 , []) \ where
  (k , as) a -> if k < n then (suc k , as) else (suc k , a :: as)

inits : List A -> List (List  A)
inits s = map (flip take s) $ til (length s + 1)

tails : List A -> List (List A)
tails s = map (flip drop s) $ til (length s + 1)

break : (A -> Bool) -> List A -> List A * List A
break p [] = ([] , [])
break p as@(x :: xs) =
  if p x then ([] , as)
  else let (ys , zs) = break p xs in (x :: ys , zs)

stripPrefix : {{_ : Eq A}} -> List A -> List A -> Maybe (List A)
stripPrefix [] as = just as
stripPrefix (x :: xs) (y :: ys) =
  if x == y then stripPrefix xs ys else nothing
stripPrefix _ _ = nothing

--------------------------------------------------------------------------------
-- Index-based operations
--------------------------------------------------------------------------------

indexed : List A -> List (Nat * A)
indexed = reverse <<< flip foldl [] \ where
  [] a -> (0 , a) :: []
  xs@(h :: t) a' -> (suc (fst h) , a') :: xs

deleteAt : Nat -> List A -> List A
deleteAt n = reverse <<< snd <<< flip foldl (0 , nil) \ where
  (k , as) a -> (suc k , if k == n then as else (a :: as))

modifyAt : Nat -> (A -> A) -> List A -> List A
modifyAt n f = reverse <<< snd <<< flip foldl (0 , nil) \ where
  (k , as) a -> (suc k , if k == n then f a :: as else (a :: as))

setAt : Nat -> A -> List A -> List A
setAt n a = modifyAt n (const a)

insertAt : Nat -> A -> List A -> List A
insertAt n a' = reverse <<< snd <<< flip foldl (0 , nil) \ where
  (k , as) a -> (suc k , if k == n then a' :: a :: as else (a :: as))

splitAt : Nat -> List A -> Pair (List A) (List A)
splitAt n as = (take n as , drop n as)

elemAt : Nat -> List A -> Maybe A
elemAt _ [] = nothing
elemAt 0 (a :: _) = just a
elemAt (suc i) (_ :: as) = elemAt i as

--------------------------------------------------------------------------------
-- Zipping functions
--------------------------------------------------------------------------------

zipWith : (A -> B -> C) -> List A -> List B -> List C
zipWith f [] _ = []
zipWith f _ [] = []
zipWith f (x :: xs) (y :: ys) = f x y :: zipWith f xs ys

zip : List A -> List B -> List (Pair A B)
zip = zipWith _,_

-- Zips together a list of heads and a list of tails.
zipCons : List A -> List (List A) -> List (List A)
zipCons heads tails =
    (zipWith _::_ heads (tails <> padding)) <> excess
  where
    -- Extra tails that will be zipped with those heads that have no
    -- corresponding tail in tails.
    padding = replicate (monus (length heads) (length tails)) []
    -- The tails that cannot be zipped because they have no corresponding
    -- head in heads.
    excess = snd (splitAt (length heads) tails)

--------------------------------------------------------------------------------
-- Predicates
--------------------------------------------------------------------------------

module _ {{_ : Eq A}} where

  isPrefixOf : List A -> List A -> Bool
  isPrefixOf [] _ = true
  isPrefixOf _ [] = false
  isPrefixOf (x :: xs) (y :: ys) = (x == y) && (isPrefixOf xs ys)

  isSuffixOf : List A -> List A -> Bool
  isSuffixOf xs ys = isPrefixOf (reverse xs) (reverse ys)

  isInfixOf : List A -> List A -> Bool
  isInfixOf [] _ = true
  isInfixOf _ [] = false
  isInfixOf as@(x :: xs) (y :: ys) =
    if x == y then isPrefixOf xs ys else isInfixOf as ys

  isSubsequenceOf : List A -> List A -> Bool
  isSubsequenceOf [] _ = true
  isSubsequenceOf _ [] = true
  isSubsequenceOf as@(x :: xs) (y :: ys) =
    if x == y then isSubsequenceOf xs ys else isSubsequenceOf as ys

--------------------------------------------------------------------------------
-- Filtering functions
--------------------------------------------------------------------------------

filter : (A -> Bool) -> List A -> List A
filter p [] = []
filter p (a :: as) = if p a then a :: filter p as else filter p as

partition : (A -> Bool) -> List A -> List A * List A
partition p = flip foldr ([] , []) \ where
  a (ts , fs) -> if p a then (a :: ts , fs) else (ts , a :: fs)

--------------------------------------------------------------------------------
-- Transformations
--------------------------------------------------------------------------------

intercalate : {{_ : Monoid A}} -> A -> List A -> A
intercalate sep [] = mempty
intercalate sep (s :: []) = s
intercalate sep (s :: rest) = s <> sep <> intercalate sep rest

intersperse : A -> List A -> List A
intersperse sep = flip foldr [] \ where
  a [] -> singleton a
  a as -> a :: sep :: as

transpose : List (List A) -> List (List A)
transpose [] = []
transpose (heads :: tails) = zipCons heads (transpose tails)

--------------------------------------------------------------------------------
-- Set-like operations
--------------------------------------------------------------------------------

deleteBy : (A -> A -> Bool) -> A -> List A -> List A
deleteBy _ _ [] = []
deleteBy eq x (y :: ys) = if eq x y then ys else (y :: deleteBy eq x ys)

nubBy : (A -> A -> Bool) -> List A -> List A
nubBy {A} eq l = nubBy' l []
  where
    elemBy : (A -> A -> Bool) -> A -> List A -> Bool
    elemBy _ _ [] = false
    elemBy eq y (x :: xs) = eq x y || elemBy eq y xs

    nubBy' : List A -> List A -> List A
    nubBy' [] _ = []
    nubBy' (y :: ys) xs =
      if elemBy eq y xs
      then nubBy' ys xs
      else (y :: nubBy' ys (y :: xs))

unionBy : (A -> A -> Bool) -> List A -> List A -> List A
unionBy eq xs ys = xs <> foldl (flip (deleteBy eq)) (nubBy eq ys) ys

delete : {{_ : Eq A}} -> A -> List A -> List A
delete = deleteBy _==_

nub : {{_ : Eq A}} -> List A -> List A
nub = nubBy _==_

union : {{_ : Eq A}} -> List A -> List A -> List A
union = unionBy _==_

--------------------------------------------------------------------------------
-- Converting to/from Maybe
--------------------------------------------------------------------------------

maybeToList : Maybe A -> List A
maybeToList nothing = []
maybeToList (just a) = singleton a

listToMaybe : List A -> Maybe A
listToMaybe [] = nothing
listToMaybe (a :: _) = just a
