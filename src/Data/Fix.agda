{-# OPTIONS --type-in-type #-}

module Data.Fix where

open import Prelude

open import Data.Container

private
  variable
    a : Type

record Fix (c : Container) : Type where
  inductive
  pattern
  constructor Fix:
  field unFix : Extension c (Fix c)

open Fix public

foldFix : {c : Container} -> (Extension c a -> a) -> Fix c -> a
foldFix alg (Fix: (Extension: s p)) = alg (Extension: s \ x -> foldFix alg (p x))
