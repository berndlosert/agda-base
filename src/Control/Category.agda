{-# OPTIONS --type-in-type #-}

module Control.Category where

-- A category C consists of:
--  * a type ob C of objects;
--  * for any two object X, Y, a type hom C X Y (called a homset) of
--    morphisms with domain X and codomain Y;
--  * a composition operator _<<<_ for composing morphisms;
--  * an identity operator id used for producing identity morphisms.

record Category : Set where
  constructor Category:
  infixr 5 _<<<_
  field
    ob : Set
    hom : ob -> ob -> Set
    _<<<_ : forall {X Y Z} -> hom Y Z -> hom X Y -> hom X Z
    id : forall {X} -> hom X X

  -- Flipped version of _<<<_.

  infixr 5 _>>>_

  _>>>_ : forall {X Y Z} -> hom X Y -> hom Y Z -> hom X Z
  f >>> g = g <<< f

open Category hiding (_<<<_; _>>>_; id) public
open Category {{...}} hiding (ob; hom) public

-- The category Sets of types and total functions.

instance
  Sets : Category
  Sets = \ where
    .ob -> Set
    .hom X Y -> X -> Y
    ._<<<_ g f -> \ x -> g (f x)
    .id x -> x

-- For every category C there is an oppossite category Op C that is just like
-- C expect that hom and _<<<_ are flipped.

open import Notation.Dual public

instance
  Dual:Category : Dual Category
  Dual:Category .Op C = let instance _ = C in \ where
    .ob -> ob C
    .hom X Y -> hom C Y X
    ._<<<_ -> _>>>_
    .id -> id

-- With this instance, we can define product categories using _*_.

open import Data.Tuple

instance
  Mul:Category : Mul Category
  Mul:Category ._*_ C C' =
    let instance _ = C; instance _ = C' in
    \ where
      .ob -> ob C * ob C'
      .hom (pair X X') (pair Y Y') -> hom C X Y * hom C' X' Y'
      ._<<<_ (pair g g') (pair f f') -> pair (g <<< f) (g' <<< f')
      .id -> pair id id

-- For every category C and every object X : ob C, hom C X X is a semigroup
-- under composition.

open import Data.Semigroup

Semigroup:<<< : forall C {X} -> Semigroup (hom C X X)
Semigroup:<<< C = Semigroup: _<<<_
  where instance _ = C

-- For every category C and object X : ob C, hom C X X is a monoid.

open import Data.Monoid

Monoid:<<< : forall C {X} -> Monoid (hom C X X)
Monoid:<<< C = let instance _ = C in \ where
  .Semigroup:Monoid -> Semigroup:<<< C
  .mempty -> id
