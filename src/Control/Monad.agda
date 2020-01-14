{-# OPTIONS --type-in-type #-}

module Control.Monad where

-- We define monads as Kleisli triples for programming convenience.

open import Control.Category
open import Data.Functor

record Monad (C : Category) (M : ob C -> ob C) : Set where
  constructor Monad:
  field
    return : forall {X} -> hom C X (M X)
    extend : forall {X Y} -> hom C X (M Y) -> hom C (M X) (M Y)

  join : forall {X} -> hom C (M (M X)) (M X)
  join = extend id
    where instance _ = C

open Monad {{...}} public

-- Every monad is a functor whose map operation is:

liftM : forall {C M X Y} {{_ : Monad C M}}
  -> hom C X Y -> hom C (M X) (M Y)
liftM {C} f = extend (return <<< f)
  where instance _ = C

-- id is trivially a monad.

Monad:id : (C : Category) -> Monad C id
Monad:id C = let instance _ = C in
  record {
    return = id;
    extend = id
  }

module _ {F : Set -> Set} {{_ : Monad Sets F}} {X Y : Set} where

  -- Defining the bind operation _>>=_ and its cousin _>>_ allows us to use do
  -- notation.

  infixl 1 _>>=_

  _>>=_ : F X -> (X -> F Y) -> F Y
  x >>= f = extend f x

  infixl 1 _>>_

  _>>_ : F X -> F Y -> F Y
  x >> y = x >>= (\ _ -> y)
