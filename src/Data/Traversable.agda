{-# OPTIONS --type-in-type #-}

module Data.Traversable where

open import Control.Applicative
open import Data.Foldable
open import Data.Functor
open import Prim

private
  variable
    A B C S : Set
    F : Set -> Set

private
  record StateL (S A : Set) : Set where
    constructor toStateL
    field fromStateL : S -> Pair S A

  open StateL

  record StateR (S A : Set) : Set where
    constructor toStateR
    field fromStateR : S -> Pair S A

  open StateR

  instance
    functorStateL : Functor (StateL S)
    functorStateL .map f mk = toStateL $ \ s0 ->
      let (s1 , v) = fromStateL mk s0 in (s1 , f v)

    functorStateR : Functor (StateR S)
    functorStateR .map f mk = toStateR $ \ s0 ->
      let (s1 , v) = fromStateR mk s0 in (s1 , f v)

    applicativeStateL : Applicative (StateL S)
    applicativeStateL .pure x = toStateL $ \ s -> (s , x)
    applicativeStateL ._<*>_ kf kv = toStateL $ \ s0 ->
      let
        (s1 , f) = fromStateL kf s0
        (s2 , v) = fromStateL kv s1
      in
        (s2 , f v)

    applicativeStateR : Applicative (StateR S)
    applicativeStateR .pure x = toStateR $ \ s -> (s , x)
    applicativeStateR ._<*>_ kf kv = toStateR $ \ s0 ->
      let
        (s1 , v) = fromStateR kv s0
        (s2 , f) = fromStateR kf s1
      in
        (s2 , f v)

record Traversable (T : Set -> Set) : Set where
  field
    {{superFunctor}} : Functor T
    {{superFoldable}} : Foldable T
    traverse : {{_ : Applicative F}} -> (A -> F B) -> T A -> F (T B)

  sequence : {{_ : Applicative F}} -> T (F A) -> F (T A)
  sequence = traverse id

  for : {{_ : Applicative F}} -> T A -> (A -> F B) -> F (T B)
  for = flip traverse

  mapPairL : (A -> B -> Pair A C) -> A -> T B -> Pair A (T C)
  mapPairL f s t = fromStateL (traverse (toStateL <<< flip f) t) s

  mapPairR : (A -> B -> Pair A C) -> A -> T B -> Pair A (T C)
  mapPairR f s t = fromStateR (traverse (toStateR <<< flip f) t) s

  scanl : (B -> A -> B) -> B -> T A -> T B
  scanl f b0 xs = snd $
    mapPairL (\ b a -> let b' = f b a in (b' , b')) b0 xs

  scanr : (A -> B -> B) -> B -> T A -> T B
  scanr f b0 xs = snd $
    mapPairR (\ b a -> let b' = f a b in (b' , b')) b0 xs

open Traversable {{...}} public
