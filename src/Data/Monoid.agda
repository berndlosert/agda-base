{-# OPTIONS --type-in-type #-}

module Data.Monoid where

-- A semigroup is a monoid when its binary operation has an identity.

open import Data.Semigroup public

record Monoid (X : Set) : Set where
  constructor Monoid:
  field
    {{Monoid:Semigroup}} : Semigroup X
    mempty : X

open Monoid {{...}} public

-- Unit forms a one-element monoid.

open import Data.Unit

instance
  Monoid:Unit : Monoid Unit
  Monoid:Unit = Monoid: tt

-- For every category C and object X : ob C, hom C X X is a monoid.

open import Control.Category
open import Data.Product

Monoid:<<< : forall C {X} -> Monoid (hom C (X , X))
Monoid:<<< C = let instance _ = C in
  record {
    Monoid:Semigroup = Semigroup:<<< C;
    mempty = id
  }

Monoid:>>> : forall C {X} -> Monoid (hom C (X , X))
Monoid:>>> C = let instance _ = C in
  record {
    Monoid:Semigroup = Semigroup:>>> C;
    mempty = id
  }

-- Functions of the form X -> Y where Y is a monoid form a monoid.

Monoid:Function : {X Y : Set} {{_ : Monoid Y}} -> Monoid (X -> Y)
Monoid:Function = record {
    Monoid:Semigroup = Semigroup:Function;
    mempty = \ x -> mempty
  }

-- Every Monoid can be viewed as a category having one object, viz. Unit,
-- and one homset, viz. hom tt tt = X. Composition in this Category is done
-- using _<>_ and mempty is the sole identity morphism.

MonoidToCategory : (X : Set) {{_ : Monoid X}} -> Category
MonoidToCategory X = record {
    ob = Unit;
    hom = \ _ -> X;
    _<<<_ = _<>_;
    id = mempty
  }

-- Monoids form a category where the morphisms are monoid homomorphisms.

open import Data.Product

Monoids : Category
Monoids = record {
    ob = exists Monoid;
    hom =  \ { ((X , _) , (Y , _)) -> X -> Y };
    _<<<_ = _<<<_;
    id = id
  }

-- A monoidal category C is one where ob C is a monoid with the proviso that
-- the associativity of _<>_ and the identityness of mempty hold up to
-- isomorphism.

Monoidal : Category -> Set
Monoidal C = Monoid (ob C)

-- The category Sets is monoidal.

open import Notation.Mul

instance
  Monoidal:Sets : Monoidal Sets
  Monoidal:Sets = Monoid: {{Semigroup: _*_}} Unit

-- A monoid object in a monoidal category is an object with two operations
-- mproduct and munit playing the role of _<>_ and mempty for monoids.

record MonoidOb
    (C : Category)
    {{_ : Monoidal C}}
    (X : ob C)
    : Set
  where
    constructor MonoidOb:
    field
      mproduct : hom C (X <> X , X)
      munit : hom C (mempty , X)

open MonoidOb {{...}} public

-- Every monoid is a monoid object in Sets.

MonoidIsMonoibOb : (X : Set) {{_ : Monoid X}} -> MonoidOb Sets X
MonoidIsMonoibOb X = MonoidOb: (uncurry _<>_) (\ _ -> mempty)
