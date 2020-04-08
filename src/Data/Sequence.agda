{-# OPTIONS --type-in-type #-}

module Data.Sequence where

open import Data.Bool
open import Data.Either
open import Data.Foldable public
open import Data.Function
open import Data.Maybe
open import Data.Nat
open import Data.Ord
open import Data.Pair
open import Data.Unit

private variable A : Set

record Sequence (S A : Set) : Set where
  field
    nil : S
    cons : A -> S -> S
    {{super}} : Fold S A

  singleton : A -> S
  singleton a = cons a nil

  head : S -> Maybe A
  head = leftToMaybe <<< foldlM (const left) unit

  uncons : S -> Maybe (Pair A S)
  uncons = foldr f nothing
    where
      f : A -> Maybe (Pair A S) -> Maybe (Pair A S)
      f a nothing = just (a , singleton a)
      f a (just (_ , s)) = just (a , cons a s)

  tail : S -> Maybe S
  tail = maybe nothing (just <<< snd) <<< uncons

  reverse : S -> S
  reverse = foldl (flip cons) nil

  replicate : Nat -> A -> S
  replicate n a = applyN (cons a) n nil

  infixr 5 _++_
  _++_ : S -> S -> S
  s1 ++ s2 = foldr f nil s1
    where
      f : A -> S -> S
      f a s = cons a (if null s then s2 else s)

  snoc : S -> A -> S
  snoc s a = s ++ singleton a

  intersperse : A -> S -> S
  intersperse sep = foldr f nil
    where
      f : A -> S -> S
      f a s = if null s then cons a s else cons a (cons sep s)

  takeWhile : (A -> Bool) -> S -> S
  takeWhile p = reverse <<< untag <<< foldlM f nil
    where
      f : S -> A -> Either S S
      f s a = if p a then right (cons a s) else left s

  dropWhile : (A -> Bool) -> S -> S
  dropWhile p = reverse <<< foldl f nil
    where
      f : S -> A -> S
      f s a = if p a then s else cons a s

  take : Nat -> S -> S
  take n = reverse <<< snd <<< untag <<< foldlM f (0 , nil)
    where
      f : Pair Nat S -> A -> Either (Pair Nat S) (Pair Nat S)
      f (k , s) a =
        if k < n then right (suc k , cons a s) else left (suc k , s)

  drop : Nat -> S -> S
  drop n = reverse <<< snd <<< foldl f (0 , nil)
    where
      f : Pair Nat S -> A -> Pair Nat S
      f (k , s) a = if k < n then (suc k , s) else (suc k , cons a s)

  deleteAt : Nat -> S -> S
  deleteAt n = reverse <<< snd <<< foldl f (0 , nil)
    where
      f : Pair Nat S -> A -> Pair Nat S
      f (k , s) a = (suc k , if k == n then s else cons a s)

  modifyAt : Nat -> (A -> A) -> S -> S
  modifyAt n f = reverse <<< snd <<< foldl g (0 , nil)
    where
      g : Pair Nat S -> A -> Pair Nat S
      g (k , s) a = (suc k , if k == n then cons (f a) s else cons a s)

  setAt : Nat -> A -> S -> S
  setAt n a = modifyAt n (const a)

  insertAt : Nat -> A -> S -> S
  insertAt n a' = reverse <<< snd <<< foldl f (0 , nil)
    where
      f : Pair Nat S -> A -> Pair Nat S
      f (k , s) a = (suc k , if k == n then cons a' (cons a s) else cons a s)

open Sequence {{...}} public

Sequential : (Set -> Set) -> Set
Sequential T = forall {A} -> Sequence (T A) A
