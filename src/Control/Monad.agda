{-# OPTIONS --type-in-type #-}

module Control.Monad where

-- A functor F : ob C -> ob C is a monad when it comes with two natural
-- transformations join and return obeying the monad laws.

open import Control.Category
open import Data.Functor

record Monad (C : Category) (F : ob C -> ob C) : Set where
  constructor Monad:
  field
    {{instance:Functor}} : Functor C C F
    join : {X : ob C} -> hom C (F (F X)) (F X)
    return : {X : ob C} -> hom C X (F X)

  extend : {X Y : ob C} -> hom C X (F Y) -> hom C (F X) (F Y)
  extend f = let instance _ = C in map f >>> join

open Monad {{...}} hiding (instance:Functor) public

-- A convenient constructor of monad instances that defines join and
-- instance:Functor in terms of extend.

Triple: : forall {C F}
  -> (forall {X Y} -> hom C X (F Y) -> hom C (F X) (F Y))
  -> (forall {X} -> hom C X (F X))
  -> Monad C F
Triple: {C} ext ret = let instance _ = C in
  record {
    instance:Functor = Functor: \ f -> ext (ret <<< f);
    join = ext id;
    return = ret
  }

-- For every category C, C ^ C is a monoidal category where the tensor is
-- functor composition and the identity is the identity functor.

open import Data.Semigroup
open import Data.Monoid

Monadic : (C : Category) -> Monoidal (C ^ C)
Monadic C = Monoid: {{Semigroup: _>>>_}} id

-- Monads are monoids in the category of endofunctors. What's the problem?

MonadIsMonoidOb : forall {C} F {{_ : Monad C F}}
  -> MonoidOb (C ^ C) {{Monadic C}} F
MonadIsMonoidOb F = MonoidOb: join return

-- Kleisli F is the Kleisli category of a monad F.

Kleisli : forall {C} F {{_ : Monad C F}} -> Category
Kleisli {C} F = let instance _ = C in
  record {
    ob = ob C;
    hom = \ X Y -> hom C X (F Y);
    _<<<_ = \ g f -> extend g <<< f;
    id = return
  }

-- id is trivially a monad.

Monad:id : (C : Category) -> Monad C id
Monad:id C = let instance _ = C in
  record {
    instance:Functor = Functor:id C;
    join = id;
    return = id
  }

module _ {F : Set -> Set} {{_ : Monad Sets F}} where

  -- Defining the bind operation _>>=_ and its cousin _>>_ allows us to use do
  -- notation.

  infixl 1 _>>=_

  _>>=_ : forall {X Y} -> F X -> (X -> F Y) -> F Y
  x >>= f = extend f x

  infixl 1 _>>_

  _>>_ : forall {X Y} -> F X -> F Y -> F Y
  x >> y = x >>= (\ _ -> y)
