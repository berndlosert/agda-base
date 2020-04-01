{-# OPTIONS --type-in-type #-}

module Data.Sequence where

open import Prelude

open import Data.Foldable public

record Sequence (S A : Set) : Set where
  field
    nil : S
    cons : A -> S -> S
    {{super}} : Foldable S A

  singleton : A -> S
  singleton a = cons a nil

  head : S -> Maybe A
  head = leftToMaybe <<< foldlM (const left) unit

  uncons : S -> Maybe (A * S)
  uncons = foldr f nothing
    where
      f : A -> Maybe (A * S) -> Maybe (A * S)
      f a nothing = just (a , singleton a)
      f a (just (_ , s)) = just (a , cons a s)

  tail : S -> Maybe S
  tail = maybe nothing (just <<< snd) <<< uncons

  reverse : S -> S
  reverse = foldl (flip cons) nil

  replicate : Nat -> A -> S
  replicate n a = applyN (cons a) n nil

  append : S -> S -> S
  append s1 s2 = foldr f nil s1
    where
      f : A -> S -> S
      f a s = cons a (if null s then s2 else s)

  snoc : S -> A -> S
  snoc s a = append s (singleton a)

  concat : List S -> S
  concat = foldr append nil

  intersperse : A -> S -> S
  intersperse sep = foldr f nil
    where
      f : A -> S -> S
      f a s = if null s then cons a s else cons a (cons sep s)

  intercalate : S -> List S -> S
  intercalate sep [] = nil
  intercalate sep (s :: []) = s
  intercalate sep (s :: rest) = append (append s sep) (intercalate sep rest)

  takeWhile : (A -> Bool) -> S -> S
  takeWhile p = reverse <<< untag <<< foldlM f nil
    where
      f : S -> A -> S + S
      f s a = if p a then right (cons a s) else left s

  dropWhile : (A -> Bool) -> S -> S
  dropWhile p = reverse <<< foldl f nil
    where
      f : S -> A -> S
      f s a = if p a then s else cons a s

  take : Nat -> S -> S
  take n = reverse <<< snd <<< untag <<< foldlM f (0 , nil)
    where
      f : Nat * S -> A -> Nat * S + Nat * S
      f (k , s) a =
        if k < n then right (suc k , cons a s) else left (suc k , s)

  drop : Nat -> S -> S
  drop n = reverse <<< snd <<< foldl f (0 , nil)
    where
      f : Nat * S -> A -> Nat * S
      f (k , s) a = if k < n then (suc k , s) else (suc k , cons a s)

  inits : S -> List S
  inits s = map (flip take s) $ til (length s + 1)

  tails : S -> List S
  tails s = map (flip drop s) $ til (length s + 1)

  deleteAt : Nat -> S -> S
  deleteAt n = reverse <<< snd <<< foldl f (0 , nil)
    where
      f : Nat * S -> A -> Nat * S
      f (k , s) a = (suc k , if k == n then s else cons a s)

  modifyAt : Nat -> (A -> A) -> S -> S
  modifyAt n f = reverse <<< snd <<< foldl g (0 , nil)
    where
      g : Nat * S -> A -> Nat * S
      g (k , s) a = (suc k , if k == n then cons (f a) s else cons a s)

  setAt : Nat -> A -> S -> S
  setAt n a = modifyAt n (const a)

  insertAt : Nat -> A -> S -> S
  insertAt n a' = reverse <<< snd <<< foldl f (0 , nil)
    where
      f : Nat * S -> A -> Nat * S
      f (k , s) a = (suc k , if k == n then cons a' (cons a s) else cons a s)

open Sequence {{...}} public

instance
  sequenceList : forall {A} -> Sequence (List A) A
  sequenceList .nil = []
  sequenceList .cons = _::_

  sequenceString : Sequence String Char
  sequenceString .nil = ""
  sequenceString .cons c s = pack (c :: unpack s)
