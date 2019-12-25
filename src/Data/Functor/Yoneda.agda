{-# OPTIONS --type-in-type #-}

module Data.Functor.Yoneda where

-- The type Yoneda C F X can be viewed as the partial application of map to
-- its second argument (assuming F is a functor).

open import Control.Category
open import Control.Monad
open import Data.Functor

Yoneda : (C : Category) -> (ob C -> Set) -> ob C -> Set
Yoneda C F X = forall {Y} -> hom C X Y -> F Y

-- Yoneda C F is a functor.

Functor:Yoneda : (C : Category) (F : ob C -> Set)
  -> Functor C Sets (Yoneda C F)
Functor:Yoneda C F .map f alpha g = alpha (f >>> g)
  where instance _ = C

-- The Yoneda lemma states that F X ~= Yoneda C F X. The -> direction
-- of this isomorphism is called lift.
lift : forall {C F X} {{_ : Functor C Sets F}} -> F X -> Yoneda C F X
lift y f = map f y

-- The <- direction of the Yoneda lemma isomorphism is called lower.
lower : forall {C F X} -> Yoneda C F X -> F X
lower {C} t = t id
  where instance _ = C
