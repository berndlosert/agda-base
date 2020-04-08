{-# OPTIONS --type-in-type #-}

module Data.List where


private variable A B C : Set

module List where
  open import Agda.Builtin.List public
    using (List; [])
    renaming (_∷_ to _::_)

  open import Data.Nat
    using (Nat; suc)

  open import Prelude
    hiding (map)

  append : List A -> List A -> List A
  append [] ys = ys
  append (x :: xs) ys = x :: append xs ys

  foldMap : {{_ : Monoid B}} -> (A -> B) -> List A -> B
  foldMap f [] = mempty
  foldMap f (a :: as) = f a <> foldMap f as

  foldr : (A -> B -> B) -> B -> List A -> B
  foldr f b [] = b
  foldr f b (a :: as) = f a (foldr f b as)

  foldl : (B -> A -> B) -> B -> List A -> B
  foldl f b [] = b
  foldl f b (a :: as) = foldl f (f b a) as

  map : (A -> B) -> List A -> List B
  map f [] = []
  map f (a :: as) = f a :: map f as

  singleton : A -> List A
  singleton a = a :: []

  ap : List (A -> B) -> List A -> List B
  ap [] _ = []
  ap _ [] = []
  ap (f :: fs) (x :: xs) = f x :: ap fs xs

  concatMap : (A -> List B) -> List A -> List B
  concatMap k [] = []
  concatMap k (x :: xs) = append (k x) (concatMap k xs)

  concat : List (List A) -> List A
  concat = concatMap id

  til : Nat -> List Nat
  til 0 = []
  til (suc n) = append (til n) (singleton n)

  range : Nat -> Nat -> List Nat
  range m n with compare m n
  ... | GT = []
  ... | EQ = singleton n
  ... | LT = map (_+ m) $ til $ suc (n - m)

  scanr : (A -> B -> B) -> B -> List A -> List B
  scanr f b [] = b :: []
  scanr f b (a :: as) with scanr f b as
  ... | [] = []
  ... | (x :: xs) = f a x :: x :: xs

  scanl : (B -> A -> B) -> B -> List A -> List B
  scanl f b [] = singleton b
  scanl f b (a :: as) = b :: scanl f (f b a) as

  and : List Bool -> Bool
  and [] = false
  and (false :: bs) = false
  and (true :: bs) = and bs

  or : List Bool -> Bool
  or [] = true
  or (true :: bs) = true
  or (false :: bs) = or bs

  any : forall {A} -> (A -> Bool) -> List A -> Bool
  any f as = or (map f as)

  all : forall {A} -> (A -> Bool) -> List A -> Bool
  all f as = and (map f as)

  length : forall {A} -> List A -> Nat
  length = foldl (\ len _ -> len + 1) 0

  filter : (A -> Bool) -> List A -> List A
  filter p [] = []
  filter p (a :: as) = if p a then a :: filter p as else as

  find : (A -> Bool) -> List A -> Maybe A
  find p as with filter p as
  ... | [] = nothing
  ... | (a :: _) = just a

  partition : (A -> Bool) -> List A -> Pair (List A) (List A)
  partition p xs = foldr (select p) ([] , []) xs
    where
      select : (A -> Bool) -> A -> Pair (List A) (List A) -> Pair (List A) (List A)
      select p a (ts , fs) with p a
      ... | true = (a :: ts , fs)
      ... | false = (ts , a :: fs)

  take : Nat -> List A -> List A
  take 0 _ = []
  take (suc n) [] = []
  take (suc n) (x :: xs) = x :: take n xs

  drop : Nat -> List A -> List A
  drop 0 as = as
  drop (suc n) [] = []
  drop (suc n) (_ :: as) = drop n as

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

  tails : List A -> List (List A)
  tails [] = singleton []
  tails as@(x :: xs) = as :: tails xs

  takeWhile : (A -> Bool) -> List A -> List A
  takeWhile _ [] = []
  takeWhile p (a :: as) with p a
  ... | true = a :: takeWhile p as
  ... | false = []

  dropWhile : (A -> Bool) -> List A -> List A
  dropWhile _ [] = []
  dropWhile p xs@(y :: ys) with p y
  ... | true = dropWhile p ys
  ... | false = ys

  --deleteBy : (A -> A -> Bool) -> A -> List A -> List A
  --deleteBy _ _ [] = []
  --deleteBy eq x (y :: ys) = if eq x y then ys else y :: deleteBy eq x ys

  --nubBy : (A -> A -> Bool) -> List A -> List A
  --nubBy {A} eq l = nubBy' l []
  --  where
  --    elemBy : (A -> A -> Bool) -> A -> List A -> Bool
  --    elemBy _ _ [] = false
  --    elemBy eq y (x :: xs) = eq x y || elemBy eq y xs
  --
  --    nubBy' : List A -> List A -> List A
  --    nubBy' [] _ = []
  --    nubBy' (y :: ys) xs =
  --      if elemBy eq y xs
  --      then nubBy' ys xs
  --      else y :: nubBy' ys (y :: xs)

  --unionBy : (A -> A -> Bool) -> List A -> List A -> List A
  --unionBy eq xs ys = xs <> foldl (flip (deleteBy eq)) (nubBy eq ys) ys

  --delete : {{_ : Eq A}} -> A -> List A -> List A
  --delete = deleteBy _==_

  --nub : {{_ : Eq A}} -> List A -> List A
  --nub = nubBy _==_

  --union : {{_ : Eq A}} -> List A -> List A -> List A
  --union = unionBy _==_

  zipWith : (A -> B -> C) -> List A -> List B -> List C
  zipWith f [] _ = []
  zipWith f _ [] = []
  zipWith f (x :: xs) (y :: ys) = f x y :: zipWith f xs ys

  zip : List A -> List B -> List (Pair A B)
  zip = zipWith _,_

  -- Zips together a list of heads and a list of tails.
  --zipCons : List A -> List (List A) -> List (List A)
  --zipCons heads tails =
  --    (zipWith _::_ heads (tails <> padding)) <> excess
  --  where
  --    -- Extra tails that will be zipped with those heads that have no
  --    -- corresponding tail in tails.
  --    padding = replicate (length heads - length tails) []
  --    -- The tails that cannot be zipped because they have no corresponding
  --    -- head in heads.
  --    excess = snd (splitAt (length heads) tails)

  reverse : List A -> List A
  reverse = foldl (flip _::_) []

  --transpose : List (List A) -> List (List A)
  --transpose [] = []
  --transpose (heads :: tails) = zipCons heads (transpose tails)

  traverse : forall {F A B} {{_ : Applicative F}}
    -> (A -> F B) -> List A -> F (List B)
  traverse f [] = pure []
  traverse f (a :: as) = (| _::_ (f a) (traverse f as) |)

  traverse! : forall {F A B} {{_ : Applicative F}}
    -> (A -> F B) -> List A -> F Unit
  traverse! f = foldr (_*>_ <<< f) (pure unit)

  for! : forall {F A B} {{_ : Applicative F}}
    -> List A -> (A -> F B) -> F Unit
  for! = flip traverse!

  null : List A -> Bool
  null [] = true
  null _ = false

  isPrefixOf : {{_ : Eq A}} -> List A -> List A -> Bool
  isPrefixOf [] _ = true
  isPrefixOf _ [] = false
  isPrefixOf (x :: xs) (y :: ys) = (x == y) && (isPrefixOf xs ys)

  isSuffixOf : {{_ : Eq A}} -> List A -> List A -> Bool
  isSuffixOf xs ys = isPrefixOf (reverse xs) (reverse ys)

  isInfixOf : {{_ : Eq A}} -> List A -> List A -> Bool
  isInfixOf xs ys = any (isPrefixOf xs) (tails ys)

  indexed : List A -> List (Pair Nat A)
  indexed as = zip indices as
    where
      indices : List Nat
      indices = til (length as)

  elemAt : Nat -> List A -> Maybe A
  elemAt _ [] = nothing
  elemAt 0 (a :: _) = just a
  elemAt (suc i) (_ :: as) = elemAt i as

  deleteAt : Nat -> List A -> List A
  deleteAt i xs with i < length xs
  deleteAt 0 (y :: ys) | true = ys
  deleteAt (suc n) (y :: ys) | true = y :: deleteAt n ys
  deleteAt _ [] | true = [] -- This case should never be reached.
  ... | false = xs

open import Data.Foldable

open List public
  using (List; []; _::_)
  hiding (module List)

open import Prelude

instance
  semigroupList : Semigroup (List A)
  semigroupList ._<>_ = List.append

  monoidList : Monoid (List A)
  monoidList .mempty = []

  foldableList : Foldable List
  foldableList .foldMap = List.foldMap

  functorList : Functor List
  functorList .map = List.map

  applicativeList : Applicative List
  applicativeList .pure = List.singleton
  applicativeList ._<*>_ = List.ap

  alternativeList : Alternative List
  alternativeList .empty = mempty
  alternativeList ._<|>_ = _<>_

  monadList : Monad List
  monadList ._>>=_ = flip List.concatMap
