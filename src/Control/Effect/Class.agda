module Control.Effect.Class where

open import Prelude

private
  variable
    ctx m n : Set -> Set

--------------------------------------------------------------------------------
-- HFunctor
--------------------------------------------------------------------------------

record HFunctor (h : (Set -> Set) -> Set -> Set) : Set where
  field hmap : {{_ : Functor m}} -> (m ~> n) -> h m ~> h n

open HFunctor {{...}} public

--------------------------------------------------------------------------------
-- Effect
--------------------------------------------------------------------------------

record Effect (sig : (Set -> Set) -> Set -> Set) : Set where
  field
    thread : {{_ : Functor ctx}} {{_ : Monad m}}
      -> (ctx ∘ m ~> n ∘ ctx) -> sig m ~> sig n ∘ ctx

open Effect {{...}} public
