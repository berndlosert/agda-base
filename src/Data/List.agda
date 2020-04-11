{-# OPTIONS --type-in-type #-}

module Data.List where

private variable A B C S : Set

open import Agda.Builtin.List public
  using (List; [])
  renaming (_∷_ to _::_)

open import Control.Alternative
open import Control.Monad
open import Data.Bool
open import Data.Either
open import Data.Function
open import Data.Maybe
open import Data.Nat
open import Data.Ord
open import Data.Pair
open import Data.Ring
open import Data.Sequence
open import Data.Traversable

instance
  foldableList : Foldable List
  foldableList .foldMap f [] = mempty
  foldableList .foldMap f (a :: as) = f a <> foldMap f as

  functorList : Functor List
  functorList .map f [] = []
  functorList .map f (a :: as) = f a :: map f as

  traversableList : Traversable List
  traversableList .traverse f = foldr cons' (pure [])
    where cons' : _; cons' x ys = (| _::_ (f x) ys |)

  sequentialList : Sequential List
  sequentialList .nil = []
  sequentialList .cons = _::_
  sequentialList .singleton = _:: []
  sequentialList ._++_ xs ys = foldr _::_ ys xs
  sequentialList .snoc as a = as ++ singleton a
  sequentialList .head [] = nothing
  sequentialList .head (a :: _) = just a
  sequentialList .tail [] = nothing
  sequentialList .tail (_ :: as) = just as
  sequentialList .uncons [] = nothing
  sequentialList .uncons (a :: as) = just (a , as)
  sequentialList .reverse = foldl (flip _::_) []
  sequentialList .replicate n a = applyN (a ::_) n []
  sequentialList .intersperse sep = foldr f []
    where
      -- f : A -> List A -> List A
      f : _
      f a [] = singleton a
      f a as = a :: sep :: as
  sequentialList .takeWhile p = reverse <<< untag <<< foldlM f []
    where
      -- f : List A -> A -> Either (List A) (List A)
      f : _
      f as a = if p a then right (a :: as) else left as
  sequentialList .dropWhile p = reverse <<< foldl f []
    where
      -- f : List A -> A -> List A
      f : _
      f as a = if p a then as else (a :: as)
  sequentialList .take n = reverse <<< snd <<< untag <<< foldlM f (0 , [])
    where
      -- f : Pair Nat S -> A -> Either (Pair Nat S) (Pair Nat S)
      f : _
      f (k , s) a =
        if k < n then right (suc k , cons a s) else left (suc k , s)
  sequentialList .drop n = reverse <<< snd <<< foldl f (0 , [])
    where
      f : _
      -- f : Pair Nat S -> A -> Pair Nat S
      f (k , as) a = if k < n then (suc k , as) else (suc k , a :: as)
  sequentialList .deleteAt n = reverse <<< snd <<< foldl f (0 , nil)
    where
      -- f : Pair Nat S -> A -> Pair Nat S
      f : _
      f (k , as) a = (suc k , if k == n then as else (a :: as))
  sequentialList .modifyAt n f = reverse <<< snd <<< foldl g (0 , nil)
    where
      -- g : Pair Nat S -> A -> Pair Nat S
      g : _
      g (k , as) a = (suc k , if k == n then f a :: as else (a :: as))
  sequentialList .setAt n a = modifyAt n (const a)
  sequentialList .insertAt n a' = reverse <<< snd <<< foldl f (0 , nil)
    where
      -- f : Pair Nat S -> A -> Pair Nat S
      f : _
      f (k , as) a = (suc k , if k == n then a' :: a :: as else (a :: as))
  sequentialList .isPrefixOf [] _ = true
  sequentialList .isPrefixOf _ [] = false
  sequentialList .isPrefixOf (x :: xs) (y :: ys) =
    (x == y) && (isPrefixOf xs ys)
  sequentialList .isSuffixOf xs ys = isPrefixOf (reverse xs) (reverse ys)
  sequentialList .isInfixOf [] _ = true
  sequentialList .isInfixOf _ [] = false
  sequentialList .isInfixOf as@(x :: xs) (y :: ys) =
    if x == y then isPrefixOf xs ys else isInfixOf as ys
  sequentialList .isSubsequenceOf [] _ = true
  sequentialList .isSubsequenceOf _ [] = true
  sequentialList .isSubsequenceOf as@(x :: xs) (y :: ys) =
    if x == y then isSubsequenceOf xs ys else isSubsequenceOf as ys
  sequentialList .null [] = true
  sequentialList .null _ = false
  sequentialList .length = foldr (const suc) 0
  sequentialList .filter p [] = []
  sequentialList .filter p (a :: as) =
    if p a then a :: filter p as else filter p as
  sequentialList .partition p xs = foldr select ([] , []) xs
    where
      select : _
      select a (ts , fs) = if p a then (a :: ts , fs) else (ts , a :: fs)

  semigroupList : Semigroup (List A)
  semigroupList ._<>_ = _++_

  monoidList : Monoid (List A)
  monoidList .mempty = []

  applicativeList : Applicative List
  applicativeList .pure = singleton
  applicativeList ._<*>_ = \ where
    [] _ -> []
    _ [] -> []
    (f :: fs) (x :: xs) -> f x :: (fs <*> xs)

  alternativeList : Alternative List
  alternativeList .empty = mempty
  alternativeList ._<|>_ = _<>_

  monadList : Monad List
  monadList ._>>=_ = \ where
    [] k -> []
    (x :: xs) k -> k x ++ (xs >>= k)

til : Nat -> List Nat
til 0 = []
til (suc n) = til n ++ singleton n

inits : List A -> List (List  A)
inits s = map (flip take s) $ til (length s + 1)

tails : List A -> List (List A)
tails s = map (flip drop s) $ til (length s + 1)

concat : {{_ : Sequence S A}} -> List S -> S
concat = foldr _++_ nil

range : Nat -> Nat -> List Nat
range m n with compare m n
... | GT = []
... | EQ = singleton n
... | LT = map (_+ m) $ til $ suc (monus n m)

intercalate : {{_ : Sequence S A}} -> S -> List S -> S
intercalate sep [] = nil
intercalate sep (s :: []) = s
intercalate sep (s :: rest) = s ++ sep ++ intercalate sep rest

break : (A -> Bool) -> List A -> Pair (List A) (List A)
break p [] = ([] , [])
break p as@(x :: xs) =
  if p x then ([] , as)
  else let (ys , zs) = break p xs in (x :: ys , zs)

splitAt : Nat -> List A -> Pair (List A) (List A)
splitAt n as = (take n as , drop n as)

stripPrefix : {{_ : Eq A}} -> List A -> List A -> Maybe (List A)
stripPrefix [] as = just as
stripPrefix (x :: xs) (y :: ys) =
  if x == y then stripPrefix xs ys else nothing
stripPrefix _ _ = nothing

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

transpose : List (List A) -> List (List A)
transpose [] = []
transpose (heads :: tails) = zipCons heads (transpose tails)

indexed : List A -> List (Pair Nat A)
indexed as = zip indices as
  where
    indices : List Nat
    indices = til (length as)

elemAt : Nat -> List A -> Maybe A
elemAt _ [] = nothing
elemAt 0 (a :: _) = just a
elemAt (suc i) (_ :: as) = elemAt i as

maybeToList : Maybe A -> List A
maybeToList nothing = []
maybeToList (just a) = singleton a

listToMaybe : List A -> Maybe A
listToMaybe [] = nothing
listToMaybe (a :: _) = just a
