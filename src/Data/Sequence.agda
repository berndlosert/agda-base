{-# OPTIONS --type-in-type #-}

module Data.Sequence where

open import Prelude

open import Data.Foldable public

private variable T : Set

record Sequence (S A : Set) : Set where
  field
    nil : S
    cons : A -> S -> S
    snoc : S -> A -> S
    {{foldable}} : Foldable S A

  append : S -> S -> S
  append s1 s2 = foldr f nil s1
    where
      f : A -> S -> S
      f a s = if null s then cons a s2 else cons a s

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

  reverse : S -> S
  reverse = foldl (flip cons) nil

  replicate : Nat -> A -> S
  replicate n a = applyN (cons a) n nil

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

  deleteAt : Nat -> S -> S
  deleteAt n = reverse <<< snd <<< foldl f (0 , nil)
    where
      f : Nat * S -> A -> Nat * S
      f (k , s) a = (suc k , if k == n then s else cons a s)

  tail : S -> Maybe S
  tail s = if null s then nothing else just (deleteAt 0 s)

  inits : S -> List S
  inits s = map (flip take s) $ til (length s + 1)

  tails : S -> List S
  tails s = map (flip drop s) $ til (length s + 1)

open Sequence {{...}} public

instance
  sequenceList : forall {A} -> Sequence (List A) A
  sequenceList .nil = []
  sequenceList .cons = _::_
  sequenceList .snoc as a = as ++ singleton a

  sequenceString : Sequence String Char
  sequenceString .nil = ""
  sequenceString .cons c s = pack (c :: unpack s)
  sequenceString .snoc s c = pack (unpack s ++ singleton c)
