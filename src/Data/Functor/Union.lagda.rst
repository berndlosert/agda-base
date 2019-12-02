******************
Data.Functor.Union
******************
::

  {-# OPTIONS --type-in-type #-}

  module Data.Functor.Union where

Union is a higher-order generalization of Either. To be precise, Union [ F₁ # F₂ # … # Fₙ ] X is the disjoint union F₁ X + F₂ X + ⋯ + Fₙ X::

  open import Data.List public
  open import Data.Either public
  open import Data.Void public

  Union : List (Set -> Set) -> Set -> Set
  Union [] X = Void
  Union (F :: Fs) X = F X + Union Fs X

We need generalizations of the injections left and right and projections leftToMaybe and rightToMaybe for Union. These generalizations are provided by the following Member type class::

  open import Control.Category
  open import Data.Functor
  open import Data.Maybe.Base

  record Member (F : Set -> Set) (Fs : List (Set -> Set)) : Set where
    field
      inj : F ~> Union Fs
      prj : Union Fs ~> Maybe <<< F

  open Member {{...}} public

  instance
    Member:Cons : forall {F Fs} -> Member F (F :: Fs)
    Member:Cons .inj = left
    Member:Cons .prj (left x) = just x
    Member:Cons .prj (right u) = nothing

If the Fs are functors, then so is Union Fs. The proof is by induction on Fs::

  -- Base case
  Functor:EmptyUnion : Endofunctor Sets (Union [])
  Functor:EmptyUnion .map f ()

  -- Inductive case
  Functor:NonemptyUnion : forall {F Fs}
    -> {{_ : Endofunctor Sets F}}
    -> {{_ : Endofunctor Sets (Union Fs)}}
    -> Endofunctor Sets (Union (F :: Fs))
  Functor:NonemptyUnion .map f (left x) = left (map f x)
  Functor:NonemptyUnion .map f (right u) = right (map f u)
