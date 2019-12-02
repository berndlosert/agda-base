************
Data.Functor
************
::

  {-# OPTIONS --type-in-type #-}

  module Data.Functor where


A function ``F : ob C -> ob D`` is a functor when it has a corresponding ``map`` operation satisfying the functor laws::

  open import Control.Category

  record Functor (C D : Category) (F : ob C -> ob D) : Set where
    constructor Functor:
    field
      map : ∀ {X Y} -> hom C X Y -> hom D (F X) (F Y)

  open Functor {{...}} public

A convenient shorthand for defining endofunctors::

  Endofunctor : (C : Category) -> (ob C -> ob C) -> Set
  Endofunctor C = Functor C C

A convenient shorthand for defining profunctors::

  open import Data.Product

  Profunctor : (C D : Category) -> (ob (C × D) -> Set) -> Set
  Profunctor C D = Functor (C × D) Sets

The composition of two functors forms a functor::

  private variable B C D : Category

  Functor:∘ : ∀ G F {{_ : Functor C D G}} {{_ : Functor B C F}}
    -> Functor B D (G ∘ F)
  Functor:∘ G F .map f = map (map f)

The identity function forms a functor::

  Functor:id : (C : Category) -> Functor C C id
  Functor:id C .map = id

For any two categories ``B``, ``C`` and for every object ``X : ob C``, ``const
X : ob B -> ob C`` is a functor::

  open import Data.Function

  Functor:const : ∀ X -> Functor B C (const X)
  Functor:const {C = C} X .map = const (id {X})
    where instance _ = C

The category of categories is called ``Categories``::

  Categories : Category
  Categories = record {
      ob = Category;
      hom = \ C D -> ob C -> ob D;
      _∘_ = _∘_;
      id = id
    }

This allows us to write ``F ~> G`` for (natural) transformations::

  record Trans (C D : Category) : Set where
    infixr 2 _~>_ _=>_
    _~>_ : (F G : ob C -> ob D) -> Set
    F ~> G  = ∀ {X} -> hom D (F X) (G X)
    _=>_ = _~>_

  Trans: : (C D : Category) -> Trans C D
  Trans: C D = record {}

  open Trans {{...}} public

``D ^ C`` is the functor category of functors from ``C to D`` and natural
transformatiosn between them::

  _^_ : Category -> Category -> Category
  D ^ C = let instance _ = D; instance _ = Trans: C D in
    record {
      ob = ob C -> ob D;
      hom = _~>_;
      _∘_ = \ β α -> β ∘ α;
      id = \ {F} {X} -> id {F X}
    }

A few special endofunctor instances::

  instance
    Functor:id[Sets] : Endofunctor Sets id
    Functor:id[Sets] = Functor:id Sets

    open import Data.Void

    Functor:const[Void] : Endofunctor Sets (const Void)
    Functor:const[Void] = Functor:const {Sets} {Sets} Void

    open import Data.Unit

    Functor:const[Unit] : Endofunctor Sets (const Unit)
    Functor:const[Unit] = Functor:const {Sets} {Sets} Unit

With this, we can write ``F × G`` for coproduct of two endofunctors on ``Sets``::

  instance
    Mul:Functor : Mul (Set -> Set)
    Mul:Functor = Mul: \ F G X -> F X × G X

The product of two endofunctors is a functor::

  private variable F G : Set -> Set

  instance
    Endofunctor:Product : {{_ : Endofunctor Sets F}} {{_ : Endofunctor Sets G}}
      -> Endofunctor Sets (F × G)
    Endofunctor:Product .map f (x , y) = (map f x , map f y)

With this, we can write ``F + G`` for coproduct of two endofunctors on ``Sets``::

  open import Data.Either

  instance
    Add:Functor : Add (Set -> Set)
    Add:Functor = Add: \ F G X -> F X + G X

The coproduct of two endofunctors is a functor::

  instance
    Endofunctor:Coproduct : {{_ : Endofunctor Sets F}} 
      -> {{_ : Endofunctor Sets G}} -> Endofunctor Sets (F + G)
    Endofunctor:Coproduct .map f (left x) = left (map f x)
    Endofunctor:Coproduct .map f (right x) = right (map f x)

And this allows use to use ``~>`` for natural transformations for endofunctors on ``Sets``::

  instance
    Trans:SetsSets = Trans: Sets Sets
