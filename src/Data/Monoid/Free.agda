{-# OPTIONS --type-in-type #-}

module Data.Monoid.Free where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Data.Foldable
open import Data.Monoid.Buildable

-------------------------------------------------------------------------------
-- Re-exports
-------------------------------------------------------------------------------

open Data.Foldable public
open Data.Monoid.Buildable public

-------------------------------------------------------------------------------
-- IsFreeMonoid
-------------------------------------------------------------------------------

record IsFreeMonoid (s a : Set) : Set where
  field
    {{IsBuildable-super}} : IsBuildable s a
    {{IsFoldable-super}} : IsFoldable s a

  reverse : s -> s
  reverse = foldl (flip cons) mempty

  intersperse : a -> s -> s
  intersperse sep = flip foldr nil \ where
    a as -> if null as then singleton a else cons a (cons sep as)

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

  filter : (a -> Bool) -> s -> s
  filter p = foldr (\ a as -> if p a then cons a as else as) nil

  partition : (a -> Bool) -> s -> s * s
  partition p xs = (filter p xs , filter (not <<< p) xs)

open IsFreeMonoid {{...}} public

-------------------------------------------------------------------------------
-- FreeMonoid
-------------------------------------------------------------------------------

FreeMonoid : (Set -> Set) -> Set
FreeMonoid t = forall {a} -> IsFreeMonoid (t a) a
