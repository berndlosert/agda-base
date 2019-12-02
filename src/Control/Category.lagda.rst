****************
Control.Category
****************
::

  {-# OPTIONS --type-in-type #-}

  module Control.Category where

  open import Data.Product

A category consists of:

- a set ob C of objects;
- for any two object X, Y, a set hom X Y (called a homset) of
  morphisms with domain X and codomain Y;
- a composition operator <<< for composing morphisms;
- an identity operator id used for producing identity morphisms;

In other words::

  record Category : Set where
    constructor Category:
    field
      ob : Set
      hom : ob -> ob -> Set
      _<<<_ : {X Y Z : ob} -> hom Y Z -> hom X Y -> hom X Z
      id : {X : ob} -> hom X X

    -- Flipped version of <<<.
    _>>>_ : {X Y Z : ob} -> hom X Y -> hom Y Z -> hom X Z
    f >>> g = g <<< f

    infixr 5 _<<<_ _>>>_

  open Category hiding (_<<<_; _>>>_; id) public
  open Category {{...}} hiding (ob; hom) public

The category of sets and total functions is called Sets::

  instance
    Sets : Category
    Sets = record {
        ob = Set;
        hom = \ X Y -> X -> Y;
        _<<<_ = \ g f x -> g (f x);
        id = \ x -> x
      }

For every category C there is an oppossite category Op C that is just like C expect that hom and <<< are flipped::

  Op : Category -> Category
  Op C = let instance _ = C in record {
      ob = ob C;
      hom = \ X Y -> hom C Y X;
      _<<<_ = _>>>_;
      id = id
    }

The product of two categories C and D has as objects all pairs (X ,
Y) where X : ob C and Y : ob D; the morphisms are also pairs (f ,
g) where f is a morphism from C and g is a morphism from D::

  CategoricalProduct : Category -> Category -> Category
  CategoricalProduct C D =
    let instance _ = C; instance _ = D in
    record {
      ob = ob C × ob D;
      hom = \ { (X , W) (Y , Z) -> hom C X Y × hom D W Z };
      _<<<_ = \ { (g , k) (f , h) -> (g <<< f , k <<< h) };
      id = (id , id)
    }

This allows us to use × (or *) for creating product categories::

  instance
    Mul:Category = Mul: CategoricalProduct
