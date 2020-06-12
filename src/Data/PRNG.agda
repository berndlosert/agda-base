{-# OPTIONS --type-in-type #-}

module Data.PRNG where

open import Prelude

record PRNG (G : Set) : Set where
  field genNext : G -> Nat * G

open PRNG {{...}} public

record SPRNG (G : Set) : Set where
  field
    {{super}} : PRNG G
    genSplit : G -> G * G

open SPRNG {{...}} public
