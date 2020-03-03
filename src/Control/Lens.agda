{-# OPTIONS --type-in-type #-}

module Control.Lens where

open import Data.Pair
open import Data.Profunctor
open import Prelude

--------------------------------------------------------------------------------
-- Lenses
--------------------------------------------------------------------------------

record Strong (P : Set -> Set -> Set) : Set where
  field
    overlap {{Profunctor:Strong}} : Endoprofunctor Sets P
    strong : forall {X Y Z} -> P X Y -> P (Z * X) (Z * Y)

open Strong {{...}}

Lens : (S T X Y : Set) -> Set
Lens S T X Y = forall {P} {{_ : Strong P}} -> P X Y -> P S T

Lens' : (S X : Set) -> Set
Lens' S X = Lens S S X X

toLens : forall {S T X Y} -> (S -> X) -> (S -> Y -> T) -> Lens S T X Y
toLens view update = dimap (split view id) update <<< strong

fromLens : forall {S T X Y} -> Lens S T X Y -> (S -> X) * (S -> Y -> T)
fromLens {S} {T} {X} {Y} lens = Pair: view update
  where
    view : S -> X
    view = {!!}
    update : S -> Y -> T
    update = {!!}

--------------------------------------------------------------------------------
-- Prisms
--------------------------------------------------------------------------------

record Choice (P : Set -> Set -> Set) : Set where
  field
    overlap {{Profunctor:Choice}} : Endoprofunctor Sets P
    choice : forall {X Y Z} -> P X Y -> P (Z + X) (Z + Y)

open Choice {{...}}

Prism : (S T X Y : Set) -> Set
Prism S T X Y = forall {P} {{_ : Choice P}} -> P X Y -> P S T

Prism' : (S X : Set) -> Set
Prism' S X = Prism S S X X

--------------------------------------------------------------------------------
-- Grates
--------------------------------------------------------------------------------

record Closed (P : Set -> Set -> Set) : Set where
  field
    overlap {{Profunctor:Closed}} : Endoprofunctor Sets P
    closed : {X Y Z : Set} -> P X Y -> P (Z -> X) (Z -> Y)

open Closed {{...}}

Grate : (S T X Y : Set) -> Set
Grate S T X Y = forall {P} {{_ : Closed P}} -> P X Y -> P S T

--------------------------------------------------------------------------------
-- Traversals
--------------------------------------------------------------------------------

data Monomial (C : Nat -> Set) (X : Set) : Set where
  Monomial: : forall {n} -> C n * Vector X n -> Monomial C X

record Polynomial (P : Set -> Set -> Set) : Set where
  field
    overlap {{Profunctor:Polynomial}} : Endoprofunctor Sets P
    polynomial : forall {X Y Z} -> P X Y -> P (Monomial Z X) (Monomial Z Y)

Traversal : (S T X Y : Set) -> Set
Traversal S T X Y = forall {P} {{_ : Polynomial P}} -> P X Y -> P S T
