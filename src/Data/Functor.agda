{-# OPTIONS --type-in-type #-}

module Data.Functor where

open import Data.Function using (_<<<_; const; flip)
open import Data.Unit using (Unit; unit)

private variable A B : Set

record Functor (F : Set -> Set) : Set where
  field
    map : (A -> B) -> F A -> F B

  infixl 4 _<$>_
  _<$>_ : (A -> B) -> F A -> F B
  _<$>_ = map

  infixl 4 _<$_
  _<$_ : B -> F A -> F B
  _<$_ = map <<< const

  infixl 4 _$>_
  _$>_ : F A -> B -> F B
  _$>_ = flip _<$_

  void : F A -> F Unit
  void = unit <$_

open Functor {{...}} public

infixr 0 _~>_
_~>_ : (F G : Set -> Set) -> Set
F ~> G  = forall {A} -> F A -> G A
