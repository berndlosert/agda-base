{-# OPTIONS --type-in-type #-}

module Data.Listlike where

open import Prelude

open import Data.Foldable public

private variable T : Set

record Listlike (S A : Set) : Set where
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

  --foldr' : forall {B} -> (A * S -> B -> B) -> B -> S -> B
  --foldr' {B} f b = snd <<< foldr g (nil , b)
  --  where
  --    g : A -> S * B -> S * B
  --    g a (s , b') = (cons a s , f (a , s) b')

  --foldl' : forall {B} -> (B -> S * A -> B) -> B -> S -> B
  --foldl' {B} f b = snd <<< foldl g (nil , b)
  --  where
  --    g : S * B -> A -> S * B
  --    g (s , b') a = (snoc a s , f b' (s , a))

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

  deleteAt : Nat -> S -> S
  deleteAt n = reverse <<< snd <<< foldl f (0 , nil)
    where
      f : Nat * S -> A -> Nat * S
      f (k , s) a = (suc k , if k == n then s else cons a s)

  tail : S -> Maybe S
  tail s = if null s then nothing else just (deleteAt 0 s)

  inits : S -> List S
  inits s = map (flip take s) $ til (length s + 1)

open Listlike {{...}} public

instance
  listlikeList : forall {A} -> Listlike (List A) A
  listlikeList .nil = []
  listlikeList .cons = _::_
  listlikeList .snoc as a = as ++ singleton a


  listlikeString : Listlike String Char
  listlikeString .nil = ""
  listlikeString .cons c s = pack (c :: unpack s)
  listlikeString .snoc s c = pack (unpack s ++ singleton c)
