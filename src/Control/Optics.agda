{-# OPTIONS --type-in-type #-}

module Control.Optics where

open import Data.Pair
open import Data.Profunctor
open import Prelude

--------------------------------------------------------------------------------
-- Adapters
--------------------------------------------------------------------------------

Adapter : (X Y S T : Set) -> Set
Adapter X Y S T = forall {P} {{_ : Endoprofunctor Sets P}}
  -> P X Y -> P S T

Iso : (X Y : Set) -> Set
Iso X Y = Adapter X X Y Y

Adapter: : forall {X Y S T} -> (S -> X) -> (Y -> T) -> Adapter X Y S T
Adapter: from to = bimap from to

instance
  Profunctor:Adapter : forall {X Y} -> Endoprofunctor Sets (Adapter X Y)
  Profunctor:Adapter .bimap f g adapter = bimap f g <<< adapter

--------------------------------------------------------------------------------
-- Lenses
--------------------------------------------------------------------------------

record Strong (P : Set -> Set -> Set) : Set where
  field
    overlap {{Profunctor:Strong}} : Endoprofunctor Sets P
    strong : forall {X Y Z} -> P X Y -> P (Z * X) (Z * Y)

open Strong {{...}} public

Lens : (X Y S T : Set) -> Set
Lens X Y S T = forall {P} {{_ : Strong P}} -> P X Y -> P S T

Lens' : (X S : Set) -> Set
Lens' X S = Lens X X S S

lens : forall {X Y S T} -> (S -> X) -> (S -> Y -> T) -> Lens X Y S T
lens get put = bimap (split id get) (uncurry put) <<< strong

--------------------------------------------------------------------------------
-- Prisms
--------------------------------------------------------------------------------

record Choice (P : Set -> Set -> Set) : Set where
  field
    overlap {{Profunctor:Choice}} : Endoprofunctor Sets P
    choice : forall {X Y Z} -> P X Y -> P (Z + X) (Z + Y)

open Choice {{...}} public

Prism : (X Y S T : Set) -> Set
Prism X Y S T = forall {P} {{_ : Choice P}} -> P X Y -> P S T

Prism' : (S X : Set) -> Set
Prism' S X = Prism S S X X

--------------------------------------------------------------------------------
-- Grates
--------------------------------------------------------------------------------

record Closed (P : Set -> Set -> Set) : Set where
  field
    overlap {{Profunctor:Closed}} : Endoprofunctor Sets P
    closed : {X Y Z : Set} -> P X Y -> P (Z -> X) (Z -> Y)

open Closed {{...}} public

Grate : (X Y S T : Set) -> Set
Grate X Y S T = forall {P} {{_ : Closed P}} -> P X Y -> P S T

--------------------------------------------------------------------------------
-- Traversals
--------------------------------------------------------------------------------

data Monomial (C : Nat -> Set) (X : Set) : Set where
  Monomial: : forall {n} -> C n * Vector X n -> Monomial C X

record Polynomial (P : Set -> Set -> Set) : Set where
  field
    overlap {{Profunctor:Polynomial}} : Endoprofunctor Sets P
    polynomial : forall {X Y Z} -> P X Y -> P (Monomial Z X) (Monomial Z Y)

open Polynomial {{...}} public

Traversal : (X Y S T : Set) -> Set
Traversal X Y S T = forall {P} {{_ : Polynomial P}} -> P X Y -> P S T
