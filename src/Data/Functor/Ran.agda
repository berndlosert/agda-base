{-# OPTIONS --type-in-type #-}

module Data.Functor.Ran where

open import Control.Category
open import Data.Functor

-- Ran F G is a generalization of Yoneda C F X. It an exponential object (with
-- exponent F and base G) in the Monadic monoidal category Sets ^ Sets. It 
-- is also the right Kan extension of G along F. More generally, we have
-- the adjunction F >>>_ -| Ran F.
Ran : {C : Category} (F : ob C → ob C) {{_ : Functor C C F}}
  (G : ob C → Set) -> ob C → Set
Ran {C} F G X = {Y : ob C} -> hom C X (F Y) -> G Y

-- Ran F G is a functor in the same way that Yoneda C F X is.
Functor:Ran : {C : Category} (F : ob C → ob C) {{_ : Functor C C F}}
  (G : ob C → Set) -> Functor C Sets (Ran F G)
Functor:Ran {C} F G .map f alpha g = alpha (f >>> g)
  where instance _ = C
