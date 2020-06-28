{-# OPTIONS --type-in-type #-}

module Control.Effect.Class where

open import Prelude

private
  variable
    Ctx M N : Set -> Set

--------------------------------------------------------------------------------
-- HFunctor
--------------------------------------------------------------------------------

record HFunctor (H : (Set -> Set) -> Set -> Set) : Set where
  field hmap : {{_ : Functor M}} -> (M ~> N) -> H M ~> H N

open HFunctor {{...}} public

--------------------------------------------------------------------------------
-- Effect
--------------------------------------------------------------------------------

record Effect (Sig : (Set -> Set) -> Set -> Set) : Set where
  field
    thread : {{_ : Functor Ctx}} {{_ : Monad M}}
      -> (Ctx ∘ M ~> N ∘ Ctx) -> Sig M ~> Sig N ∘ Ctx

open Effect {{...}} public
