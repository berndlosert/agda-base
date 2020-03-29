{-# OPTIONS --type-in-type #-}

module Data.Listlike where

open import Prelude

open import Data.Foldable public

record Listlike (S A : Set) : Set where
  field
    nil : S
    cons : A -> S -> S
    snoc : S -> A -> S
    {{foldable}} : Foldable S A

  reverse : S -> S
  reverse = foldl (flip cons) nil

  replicate : Nat -> A -> S
  replicate n a = applyN (cons a) n nil

  takeWhile : (A -> Bool) -> S -> S
  takeWhile p = reverse <<< foldl f nil
    where
      f : S -> A -> S
      f s a with p a
      ... | true = cons a s
      ... | false = s

  dropWhile : (A -> Bool) -> S -> S
  dropWhile p = reverse <<< snd <<< foldl f (true , nil)
    where
      f : Bool * S -> A -> Bool * S
      f (b , s) a with b | p a
      ... | true | true = (true , s)
      ... | true | false = (false , cons a s)
      ... | false | _ = (false , cons a s)

  take : Nat -> S -> S
  take n = reverse <<< snd <<< foldl f (0 , nil)
    where
      f : Nat * S -> A -> Nat * S
      f (k , s) a = (suc k , if k < n then cons a s else s)

  deleteAt : Nat -> S -> S
  deleteAt n = reverse <<< snd <<< foldl f (0 , nil)
    where
      f : Nat * S -> A -> Nat * S
      f (k , s) a = (suc k , if k == n then s else cons a s)

  tail : S -> Maybe S
  tail s = if null s then nothing else just (deleteAt 0 s)

  inits : S -> List S
  inits s = (snd $ foldl f (nil , identity) s) []
    where
      f : S * (List S -> List S) -> A -> S * (List S -> List S)
      f (s , acc) a = let s' = snoc s a in (s' , acc <<< (s' ::_ ))

open Listlike {{...}} public

instance
  listlikeList : forall {A} -> Listlike (List A) A
  listlikeList .nil = []
  listlikeList .cons = _::_
  listlikeList .snoc as a = as ++ singleton a
