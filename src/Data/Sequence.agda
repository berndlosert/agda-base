{-# OPTIONS --type-in-type #-}

module Data.Sequence where

open import Data.Bool
open import Data.Either
open import Data.Function
open import Data.Maybe
open import Data.Nat
open import Data.Ord
open import Data.Pair
open import Data.Unit

private variable A : Set

record Sequence (S A : Set) : Set where
  infixr 5 _++_
  field
    -- Basic constructors
    nil : S
    cons : A -> S -> S
    singleton : A -> S
    _++_ : S -> S -> S
    snoc : S -> A -> S
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
    null : S -> Bool
    length : S -> Nat
    -- Filter
    filter : (A -> Bool) -> S -> S

open Sequence {{...}} public

Sequential : (Set -> Set) -> Set
Sequential T = forall {A} -> Sequence (T A) A
