{-# OPTIONS --type-in-type #-}

module Data.Functor.Yoneda where

open import Prelude

private
  variable
    A B : Set
    F : Set -> Set

-- The type Yoneda F A can be viewed as the partial application of map to
-- its second argument (assuming F is a functor).
Yoneda : (Set -> Set) -> Set -> Set
Yoneda F A = ∀ {B} -> (A -> B) -> F B

-- Yoneda F is a functor.
instance
  functorYoneda : Functor (Yoneda F)
  functorYoneda .map f t g = t (g <<< f)

-- The Yoneda lemma states that F A ~= Yoneda C F A. The -> direction
-- of this isomorphism is called lift.
lift : {{_ : Functor F}} -> F A -> Yoneda F A
lift y f = map f y

-- The <- direction of the Yoneda lemma isomorphism is called lower.
lower : Yoneda F A -> F A
lower t = t id
