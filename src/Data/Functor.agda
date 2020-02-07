{-# OPTIONS --type-in-type #-}

module Data.Functor where

-- A function F : ob C -> ob D is a functor when it has a corresponding map
-- operation satisfying the functor laws.

open import Control.Category public

record Functor (C D : Category) (F : ob C -> ob D) : Set where
  constructor Functor:
  field
    map : forall {X Y} -> hom C X Y -> hom D (F X) (F Y)

open Functor {{...}} public

-- A convenient shorthand for defining endofunctors.

Endofunctor : (C : Category) -> (ob C -> ob C) -> Set
Endofunctor C = Functor C C

-- An infix synonym for map for functors of type Endofunctor Sets.

infixl 24 _<$>_

_<$>_ : forall {X Y F} {{_ : Endofunctor Sets F}}
  -> (X -> Y) -> F X -> F Y
_<$>_ = map

-- The composition of two functors forms a functor.

Functor:<<< : forall {B C D} G F
  -> {{_ : Functor C D G}}
  -> {{_ : Functor B C F}}
  -> Functor B D (G <<< F)
Functor:<<< G F .map f = map (map f)

-- The identity function forms a functor.

Functor:id : (C : Category) -> Functor C C id
Functor:id C .map = id

-- For any two categories B, C and for every object X : ob C, the function
-- const X : ob B -> ob C forms a functor.

open import Data.Function

Functor:const : forall {B C} X -> Functor B C (const X)
Functor:const {B} {C} X .map = const (id {X})
  where instance _ = C

-- Let C be a category and let F be an endofunctor on C. Then the composition
-- F <<< F <<< ... <<< F, where F appears n times, is also an endofunctor on C.

open import Data.Nat.Base

Functor:nest : forall n {C F} {{_ : Endofunctor C F}}
  -> Endofunctor C (nest n F)
Functor:nest zero .map f = f
Functor:nest (suc n) .map f = map (map {{Functor:nest n}} f)

-- The category of categories is called Categories.

Categories : Category
Categories = record {
    ob = Category;
    hom = \ C D -> ob C -> ob D;
    _<<<_ = _<<<_;
    id = id
  }

-- This allows us to write F ~> G for (natural) transformations.

record Trans (C D : Category) : Set where
  infixr 2 _~>_
  _~>_ : (F G : ob C -> ob D) -> Set
  F ~> G  = forall {X} -> hom D (F X) (G X)

open Trans {{...}} public

-- We use this to define Trans instances.

Trans: : (C D : Category) -> Trans C D
Trans: C D = record {}

-- This is useful when dealing with (natural) transformations between
-- endofunctors.

Transendo : Category -> Set
Transendo C = Trans C C

Transendo: : (C : Category) -> Transendo C
Transendo: C = record {}

-- D ^ C is the functor category of functors from C to D and natural
-- transformatiosn between them.

open import Notation.Exp public

instance
  Exp:Category : Exp Category Category Category
  Exp:Category ._^_ D C =
    let instance _ = D; instance _ = Trans: C D
    in record {
      ob = ob C -> ob D;
      hom = _~>_;
      _<<<_ = \ beta alpha -> beta <<< alpha;
      id = \ {F} {X} -> id {F X}
    }

-- The category Sets ^ Sets is special enough to warrant a Category instance.

instance
  Sets^Sets : Category
  Sets^Sets = Sets ^ Sets

-- A few special endofunctor instances.

open import Data.Void
open import Data.Unit

Functor:const[Void] : Endofunctor Sets (const Void)
Functor:const[Void] = Functor:const {Sets} {Sets} Void

Functor:const[Unit] : Endofunctor Sets (const Unit)
Functor:const[Unit] = Functor:const {Sets} {Sets} Unit

-- This allows use to use ~> for natural transformations for endofunctors on
-- Sets and Sets ^ Sets.

instance
  Transendo:Sets : Transendo Sets
  Transendo:Sets = Transendo: Sets

  Transendo:Sets^Sets : Transendo Sets^Sets
  Transendo:Sets^Sets = Transendo: Sets^Sets

-- hmap is just what we call the map functor of endofunctors from Sets^Sets to
-- Sets^Sets.

hmap : forall {F S T} {{_ : Endofunctor Sets^Sets F}}
  -> (S ~> T) -> F S ~> F T
hmap = map
