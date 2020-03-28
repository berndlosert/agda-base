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

  replicate : Nat -> A -> S
  replicate n a = applyN (cons a) n nil

  takeWhile : (A -> Bool) -> S -> S
  takeWhile p = foldl f nil
    where
      f : S -> A -> S
      f s a with p a
      ... | true = snoc s a
      ... | false = s

  dropWhile : (A -> Bool) -> S -> S
  dropWhile p = snd <<< foldl f (true , nil)
    where
      f : Bool * S -> A -> Bool * S
      f (b , s) a with b | p a
      ... | true | true = (true , s)
      ... | true | false = (false , snoc s a)
      ... | false | _ = (false , snoc s a)

  deleteAt : Nat -> S -> S
  deleteAt n = snd <<< foldl f (0 , nil)
    where
      f : Nat * S -> A -> Nat * S
      f (k , s) a = (suc k , if k == n then s else snoc s a)

  tail : S -> Maybe S
  tail s = if null s then nothing else just (deleteAt 0 s)

  inits : S -> List S
  inits = snd <<< foldl f (nil , [])
    where
      f : S * List S -> A -> S * List S
      f (s , acc) a = let s' = snoc s a in (s' , acc ++ singleton s')

open Listlike {{...}} public
