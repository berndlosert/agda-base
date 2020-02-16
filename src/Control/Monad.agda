{-# OPTIONS --type-in-type #-}

module Control.Monad where

-- We define monads as Kleisli triples for programming convenience.

open import Data.Functor public

record Monad (C : Category) (M : ob C -> ob C) : Set where
  constructor Monad:
  field
    overlap {{Functor:Monad}} : Endofunctor C M
    return : forall {X} -> hom C X (M X)
    extend : forall {X Y} -> hom C X (M Y) -> hom C (M X) (M Y)

  join : forall {X} -> hom C (M (M X)) (M X)
  join = extend id
    where instance _ = C

open Monad {{...}} public

-- id is trivially a monad.

Monad:id : (C : Category) -> Monad C id
Monad:id C = let instance _ = C in
  record {
    Functor:Monad = Functor:id C;
    return = id;
    extend = id
  }

-- Defining the bind operation _>>=_ and its cousin _>>_ allows us to use do
-- notation.

module _ {M : Set -> Set} {{_ : Monad Sets M}} {X Y : Set} where

  infixl 1 _>>=_ _>>_

  _>>=_ : M X -> (X -> M Y) -> M Y
  x >>= f = extend f x

  _>>_ : M X -> M Y -> M Y
  x >> y = x >>= (\ _ -> y)

-- We use _<=<_ and _>=>_ for Kleisli composition for monads on Sets.

module _ {M : Set -> Set} {{_ : Monad Sets M}} {X Y Z : Set} where

  infixl 1 _<=<_ _>=>_

  _<=<_ : (Y -> M Z) -> (X -> M Y) -> X -> M Z
  g <=< f = \ x -> f x >>= g

  _>=>_ : (X -> M Y) -> (Y -> M Z) -> X -> M Z
  f >=> g = g <=< f
