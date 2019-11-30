{-# OPTIONS --type-in-type #-}

module Control.Category where

open import Data.Product

-- A category consists of: a type ob C of objects; for any two object X Y,
-- a type hom X Y (called a homset) of morphisms with domain X and codomain Y;
-- an operator _>>>_ for composing morphisms with an identity id.
record Category : Set where
  constructor Category:
  field
    ob : Set
    hom : ob -> ob -> Set
    _>>>_ : {X Y Z : ob} -> hom X Y -> hom Y Z -> hom X Z
    id : {X : ob} -> hom X X

  _<<<_ : {X Y Z : ob} -> hom Y Z -> hom X Y -> hom X Z
  g <<< f = f >>> g

  infixr 5 _<<<_
  infixr 5 _>>>_

open Category hiding (_>>>_; _<<<_; id) public
open Category {{...}} hiding (ob; hom) public

-- The category of types and total functions is called Sets.
instance
  Sets : Category
  Sets = record {
      ob = Set;
      hom = \ X Y -> X -> Y;
      _>>>_ = \ f g x -> g (f x);
      id = \ x -> x
    }

-- For every category C there is an oppossite category Op C that is just like
-- C expect that hom and _>>>_ are flipped.
Op : Category -> Category
Op C = let instance _ = C in record {
    ob = ob C;
    hom = \ X Y -> hom C Y X;
    _>>>_ = _<<<_;
    id = id
  }

-- The product of two categories C and D has as objects all pairs (X , Y)
-- where X : ob C and Y : ob D; the morphisms are also pairs (f , g) where
-- f is a morphism from C and g is a morphism from G. 
CategoricalProduct : Category -> Category -> Category
CategoricalProduct C D =
  let instance _ = C; instance _ = D in
  record {
    ob = ob C * ob D;
    hom = \ { (X , W) (Y , Z) -> hom C X Y * hom D W Z };
    _>>>_ = \ { (f , h) (g , k) -> (f >>> g , h >>> k) };
    id = (id , id)
  }

-- This allows us to use _*_ for creating product categories.
instance Mul:Category = Mul: CategoricalProduct
