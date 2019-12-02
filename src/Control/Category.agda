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
  infixr 5 _<<<_ _>>>_
  field
    ob : Set
    hom : ob -> ob -> Set
    _<<<_ : {X Y Z : ob} -> hom Y Z -> hom X Y -> hom X Z
    id : {X : ob} -> hom X X

  _>>>_ : {X Y Z : ob} -> hom X Y -> hom Y Z -> hom X Z
  f >>> g = g <<< f

open Category hiding (_<<<_; _>>>_; id) public
open Category {{...}} hiding (ob; hom) public

-- The category Sets of types and total functions.

instance
  Sets : Category
  Sets = record {
      ob = Set;
      hom = \ X Y -> X -> Y;
      _<<<_ = \ g f x -> g (f x);
      id = \ x -> x
    }

-- For every category C there is an oppossite category Op C that is just like
-- C expect that hom and _<<<_ are flipped.

Op : Category -> Category
Op C = let instance _ = C in record {
    ob = ob C;
    hom = \ X Y -> hom C Y X;
    _<<<_ = _>>>_;
    id = id
  }

-- The product of two categories C and D has as objects all pairs (X , Y) where
-- X : ob C and Y : ob D; the morphisms are also pairs (f , g) where f is a
-- morphism from C and g is a morphism from D.

open import Data.Product

CategoricalProduct : Category -> Category -> Category
CategoricalProduct C D =
  let instance _ = C; instance _ = D in
  record {
    ob = ob C * ob D;
    hom = \ { (X , W) (Y , Z) -> hom C X Y * hom D W Z };
    _<<<_ = \ { (g , k) (f , h) -> (g <<< f , k <<< h) };
    id = (id , id)
  }

-- This instance allows us to use _*_ for creating product categories.

instance
  Mul:Category = Mul: CategoricalProduct
