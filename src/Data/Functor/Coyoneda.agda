{-# OPTIONS --type-in-type #-}

module Data.Functor.Coyoneda where


-- This is the existensial version Yoneda C F X.

open import Control.Category
open import Data.Product

Coyoneda : (C : Category) -> (ob C -> Set) -> ob C -> Set
Coyoneda C F Y = exists \ X -> F X * hom C X Y

-- Coyoneda C F is a functor.

open import Data.Functor

Functor:Coyoneda : (C : Category) (F : ob C -> Set)
  -> Functor C Sets (Coyoneda C F)
Functor:Coyoneda C F .map f (_ , x , g) = (_ , x , f <<< g)
  where instance _ = C

-- The coYoneda lemma states that F Y ~= Coyoneda C F Y. The isomorphsim
-- is witnessed by lowerCoyoneda and liftCoyoneda.

lowerCoyoneda : forall {C F X} {{_ : Functor C Sets F}}
  -> Coyoneda C F X -> F X
lowerCoyoneda (_ , x , f) = map f x

liftCoyoneda : forall {C F X} -> F X -> Coyoneda C F X
liftCoyoneda {C} y = (_ , y , id)
  where instance _ = C

-- It turns out that Coyoneda is a free construction, i.e. Coyoneda C F is the
-- free functor generated by F. This is the right adjunct of the corresponding
-- free/forgetful adjunction.

interpretCoyoneda : forall {C F G} {{_ : Functor C Sets G}} ->
  let instance _ = Trans: C Sets in
  (F ~> G) -> Coyoneda C F ~> G
interpretCoyoneda alpha (_ , x , f) = map f (alpha x)

-- This is the left adjunct.
uninterpretCoyoneda : forall {C F G} ->
  let instance _ = Trans: C Sets in
  (Coyoneda C F ~> G) -> (F ~> G)
uninterpretCoyoneda {C} alpha x = alpha (liftCoyoneda {C} x)
