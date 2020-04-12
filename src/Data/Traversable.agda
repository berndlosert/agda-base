{-# OPTIONS --type-in-type #-}

module Data.Traversable where

open import Control.Applicative public
open import Data.Foldable public
open import Data.Function

private
  variable
    A B C S : Set
    F : Set -> Set

record Accum (S A : Set) : Set where
  constructor toAccum
  field
    accum : S
    value : A

private
  record StateL (S A : Set) : Set where
    constructor toStateL
    field fromStateL : S -> Accum S A

  open StateL

  record StateR (S A : Set) : Set where
    constructor toStateR
    field fromStateR : S -> Accum S A

  open StateR

  instance
    functorStateL : Functor (StateL S)
    functorStateL .map f mk = toStateL $ \ s0 ->
      let toAccum s1 v = fromStateL mk s0 in toAccum s1 (f v)

    functorStateR : Functor (StateR S)
    functorStateR .map f mk = toStateR $ \ s0 ->
      let toAccum s1 v = fromStateR mk s0 in toAccum s1 (f v)

    applicativeStateL : Applicative (StateL S)
    applicativeStateL .pure x = toStateL $ \ s -> toAccum s x
    applicativeStateL ._<*>_ kf kv = toStateL $ \ s0 ->
      let
        toAccum s1 f = fromStateL kf s0
        toAccum s2 v = fromStateL kv s1
      in
        toAccum s2 (f v)

    applicativeStateR : Applicative (StateR S)
    applicativeStateR .pure x = toStateR $ \ s -> toAccum s x
    applicativeStateR ._<*>_ kf kv = toStateR $ \ s0 ->
      let
        toAccum s1 v = fromStateR kv s0
        toAccum s2 f = fromStateR kf s1
      in
        toAccum s2 (f v)

record Traversable (T : Set -> Set) : Set where
  field
    {{superFunctor}} : Functor T
    {{superFoldable}} : Foldable T
    traverse : {{_ : Applicative F}} -> (A -> F B) -> T A -> F (T B)

  sequence : {{_ : Applicative F}} -> T (F A) -> F (T A)
  sequence = traverse id

  for : {{_ : Applicative F}} -> T A -> (A -> F B) -> F (T B)
  for = flip traverse

  mapAccumL : (A -> B -> Accum A C) -> A -> T B -> Accum A (T C)
  mapAccumL f s t = fromStateL (traverse (toStateL <<< flip f) t) s

  mapAccumR : (A -> B -> Accum A C) -> A -> T B -> Accum A (T C)
  mapAccumR f s t = fromStateR (traverse (toStateR <<< flip f) t) s

  scanl : (B -> A -> B) -> B -> T A -> T B
  scanl f b0 xs = Accum.value $
    mapAccumL (\ b a -> let b' = f b a in toAccum b' b') b0 xs

  scanr : (A -> B -> B) -> B -> T A -> T B
  scanr f b0 xs = Accum.value $
    mapAccumR (\ b a -> let b' = f a b in toAccum b' b') b0 xs

open Traversable {{...}} public
