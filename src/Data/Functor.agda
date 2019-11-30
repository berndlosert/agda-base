{-# OPTIONS --type-in-type #-}

module Data.Functor where

open import Control.Category
open import Data.Either
open import Data.Function
open import Data.Product
open import Data.Unit
open import Data.Void

-- This notation helps us avoid having to use ob all the time.
_=>_ : Category -> Category -> Set
C => D = ob C -> ob D

-- A function F : C => D is a functor when it has a corresponding map operation
-- satisfying the functor laws.
record Functor (C D : Category) (F : C => D) : Set where
  constructor Functor:
  field
    map : {X Y : ob C} -> hom C X Y -> hom D (F X) (F Y)

open Functor {{...}} public

-- Convenience for defining endofunctors.
Endofunctor : (C : Category) -> (C => C) -> Set
Endofunctor C = Functor C C

-- Convenience for defining profunctors.
Profunctor : (C D : Category) -> (C * D => Sets) -> Set
Profunctor C D = Functor (C * D) Sets

-- The composition of two functors is a functor.
Functor:_>>>_ : {B C D : Category}
  -> (F : B => C) {{_ : Functor B C F}}
  -> (G : C => D) {{_ : Functor C D G}}
  -> Functor B D (F >>> G)
Functor:_>>>_ F G .map f = map (map f)

-- The identity function is functorial.
Functor:id : (C : Category) -> Functor C C id
Functor:id C .map = id

-- For any two categories B, C and for every object X : ob C, const X : B => C
-- is a functor.
Functor:const : {B C : Category} -> (X : ob C)
  -> Functor B C (const X)
Functor:const {B} {C} X .map = const (id {X})
  where instance _ = C

-- The category of categories is called Categories.
Categories : Category
Categories = record {
    ob = Category;
    hom = _=>_;
    _∘_ = _∘_;
    id = id
  }

-- This allows us to F ~> G for (natural) transformations.
record Trans (C D : Category) : Set where
  _~>_ : (F G : C => D) -> Set
  F ~> G  = {X : ob C} -> hom D (F X) (G X)
  infixr 2 _~>_

Trans: : (C D : Category) -> Trans C D
Trans: C D = record {}

open Trans {{...}} public

-- C :=> D is the functor category of functors from C to D and natural
-- transformatiosn between them.
_:=>_ : Category -> Category -> Category
C :=> D = let instance _ = D; instance _ = Trans: C D in
  record {
    ob = C => D;
    hom = _~>_;
    _∘_ = \ beta alpha -> beta ∘ alpha;
    id = \ {F} {X} -> id {F X}
  }

instance
  Functor:id[Sets] : Endofunctor Sets id
  Functor:id[Sets] = Functor:id Sets

  Functor:const[Void] : Endofunctor Sets (const Void)
  Functor:const[Void] = Functor:const {Sets} {Sets} Void

  Functor:const[Unit] : Endofunctor Sets (const Unit)
  Functor:const[Unit] = Functor:const {Sets} {Sets} Unit

  -- With this, we can write F * G for coproduct of two endofunctors on Sets.
  Mul:Functor : Mul (Set -> Set)
  Mul:Functor = Mul: \ F G X -> F X * G X

  -- The product of two endofunctors is a functor.
  Endofunctor:Product : {F G : Set -> Set}
    -> {{_ : Endofunctor Sets F}}
    -> {{_ : Endofunctor Sets G}}
    -> Endofunctor Sets (F * G)
  Endofunctor:Product .map f (x , y) = (map f x , map f y)

  -- With this, we can write F + G for coproduct of two endofunctors on Sets.
  Add:Functor : Add (Set -> Set)
  Add:Functor = Add: \ F G X -> F X + G X

  -- The coproduct of two endofunctors is a functor.
  Endofunctor:Coproduct : {F G : Set -> Set}
    -> {{_ : Endofunctor Sets F}}
    -> {{_ : Endofunctor Sets G}}
    -> Endofunctor Sets (F + G)
  Endofunctor:Coproduct .map f (left x) = left (map f x)
  Endofunctor:Coproduct .map f (right x) = right (map f x)

  -- And this allows use to use _~>_ for natural transformations for
  -- endofunctors on Sets.
  Trans:SetsSets = Trans: Sets Sets
