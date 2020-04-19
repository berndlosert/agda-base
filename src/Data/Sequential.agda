{-# OPTIONS --type-in-type #-}

module Data.Sequential where

open import Data.Buildable
open import Data.Eq
open import Data.Foldable
open import Prim

private variable A : Set

record IsSequential (S A : Set) : Set where
  field
    {{superIsBuildable}} : IsBuildable S A
    {{superIsFoldable}} : IsFoldable S A
    -- Destructors
    head : S -> Maybe A
    tail : S -> Maybe S
    uncons : S -> Maybe (Pair A S)
    -- Generators
    replicate : Nat -> A -> S
    -- Transformations
    reverse : S -> S
    intersperse : A -> S -> S
    -- Subsequences
    takeWhile : (A -> Bool) -> S -> S
    dropWhile : (A -> Bool) -> S -> S
    take : Nat -> S -> S
    drop : Nat -> S -> S
    -- Index-based operations
    deleteAt : Nat -> S -> S
    modifyAt : Nat -> (A -> A) -> S -> S
    setAt : Nat -> A -> S -> S
    insertAt : Nat -> A -> S -> S
    -- Predicates
    isPrefixOf : {{eq : Eq A}} -> S -> S -> Bool
    isSuffixOf : {{eq : Eq A}} -> S -> S -> Bool
    isInfixOf : {{eq : Eq A}} -> S -> S -> Bool
    isSubsequenceOf : {{eq : Eq A}} -> S -> S -> Bool
    -- Length
    length : S -> Nat
    -- Filter
    filter : (A -> Bool) -> S -> S
    partition : (A -> Bool) -> S -> Pair S S

open IsSequential {{...}} public

Sequential : (Set -> Set) -> Set
Sequential T = forall {A} -> IsSequential (T A) A
