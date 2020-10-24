{-# OPTIONS --type-in-type #-}

module Data.Sequence.View where

-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

open import Prelude

open import Data.Constraint.Nonempty

-------------------------------------------------------------------------------
-- Variables
-------------------------------------------------------------------------------

private
  variable
    a : Set
    f : Set -> Set

-------------------------------------------------------------------------------
-- ViewL
-------------------------------------------------------------------------------

infixr 5 _:<_
data ViewL (f : Set -> Set) (a : Set) : Set where
  EmptyL : ViewL f a
  _:<_ : a -> f a -> ViewL f a

instance
  Functor-ViewL : {{_ : Functor f}} -> Functor (ViewL f)
  Functor-ViewL .map _ EmptyL = EmptyL
  Functor-ViewL .map f (x :< xs) = f x :< map f xs

  NonemptyConstraint-ViewL : NonemptyConstraint (ViewL f a)
  NonemptyConstraint-ViewL .IsNonempty EmptyL = Void
  NonemptyConstraint-ViewL .IsNonempty _ = Unit

-------------------------------------------------------------------------------
-- ViewR
-------------------------------------------------------------------------------

infixr 5 _:>_
data ViewR (f : Set -> Set) (a : Set) : Set where
  EmptyR : ViewR f a
  _:>_ : f a -> a -> ViewR f a

instance
  Functor-ViewR : {{_ : Functor f}} -> Functor (ViewR f)
  Functor-ViewR .map _ EmptyR = EmptyR
  Functor-ViewR .map f (xs :> x) = map f xs :> f x

  NonemptyConstraint-ViewR : NonemptyConstraint (ViewR f a)
  NonemptyConstraint-ViewR .IsNonempty EmptyR = Void
  NonemptyConstraint-ViewR .IsNonempty _ = Unit
