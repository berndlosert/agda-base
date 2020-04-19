{-# OPTIONS --type-in-type #-}

module Data.Sequential where

open import Data.Buildable
open import Data.Either
open import Data.Eq
open import Data.Foldable
open import Data.Maybe
open import Data.Monoid
open import Data.Nat
open import Data.Semigroup
open import Data.Traversable
open import Prim

private variable A B : Set

record IsSequential (S A : Set) : Set where
  field
    {{superIsBuildable}} : IsBuildable S A
    {{superIsFoldable}} : IsFoldable S A

  -- Primitive recursion
  recurse : (A -> S -> B -> B) -> B -> S -> B
  recurse f b = snd <<< flip foldr (nil , b) \ where
    a (as , b') -> (cons a as , f a as b')

  field
    -- Destructors
    tail : S -> Maybe S
    uncons : S -> Maybe (Pair A S)
    ---- Subsequences
    --takeWhile : (A -> Bool) -> S -> S
    --dropWhile : (A -> Bool) -> S -> S
    --take : Nat -> S -> S
    --drop : Nat -> S -> S
    ---- Index-based operations
    --deleteAt : Nat -> S -> S
    --modifyAt : Nat -> (A -> A) -> S -> S
    --setAt : Nat -> A -> S -> S
    --insertAt : Nat -> A -> S -> S
    ---- Predicates
    --isPrefixOf : {{eq : Eq A}} -> S -> S -> Bool
    --isSuffixOf : {{eq : Eq A}} -> S -> S -> Bool
    --isInfixOf : {{eq : Eq A}} -> S -> S -> Bool
    --isSubsequenceOf : {{eq : Eq A}} -> S -> S -> Bool
    ---- Length
    --length : S -> Nat
    ---- Filter
    --filter : (A -> Bool) -> S -> S
    --partition : (A -> Bool) -> S -> Pair S S

  -- Destructors
  head : S -> Maybe A
  head = untag <<< foldlM (const $ left <<< just) nothing

  -- Generators
  replicate : Nat -> A -> S
  replicate n a = applyN (cons a) n nil

  -- Transformations
  reverse : S -> S
  reverse = foldl (flip cons) nil

  intersperse : A -> S -> S
  intersperse sep = flip foldr nil \ where
    a as -> if null as then singleton a else cons a (cons sep as)

open IsSequential {{...}} public

Sequential : (Set -> Set) -> Set
Sequential T = forall {A} -> IsSequential (T A) A
