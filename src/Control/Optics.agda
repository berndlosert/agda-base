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

record Exchange (X Y S T : Set) : Set where
  constructor Exchange:
  field
    from : S -> X
    to : Y -> T

instance
  Profunctor:Adapter : forall {X Y} -> Endoprofunctor Sets (Adapter X Y)
  Profunctor:Adapter .bimap f g adapter = bimap f g <<< adapter

  Profunctor:Exchange : forall {X Y} -> Endoprofunctor Sets (Exchange X Y)
  Profunctor:Exchange .bimap f g (Exchange: from to) =
    Exchange: (from <<< f) (g <<< to)

from : forall {X Y S T} -> Adapter X Y S T -> S -> X
from adapter = Exchange.from $ adapter $ Exchange: id id

to : forall {X Y S T} -> Adapter X Y S T -> Y -> T
to adapter = Exchange.to $ adapter $ Exchange: id id

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

Lens: : forall {X Y S T} -> (S -> X) -> (S -> Y -> T) -> Lens X Y S T
Lens: get put = bimap (split id get) (uncurry put) <<< strong

record Shop (X Y S T : Set) : Set where
  constructor Shop:
  field
    get : S -> X
    put : S -> Y -> T

instance
  Profunctor:Lens : forall {X Y} -> Endoprofunctor Sets (Lens X Y)
  Profunctor:Lens .bimap f g lens = bimap f g <<< lens

  Profunctor:Shop : forall {X Y} -> Endoprofunctor Sets (Shop X Y)
  Profunctor:Shop .bimap f g (Shop: get put) =
    Shop: (get <<< f) (\ s -> g <<< put (f s))

  Strong:Shop : forall {X Y} -> Strong (Shop X Y)
  Strong:Shop .strong (Shop: get put) = Shop: get' put'
    where
      get' put' : _
      get' (Pair: u s) = get s
      put' (Pair: u s) y = Pair: u (put s y)

get : forall {X Y S T} -> Lens X Y S T -> S -> X
get lens = Shop.get $ lens $ Shop: id (flip const)

put : forall {X Y S T} -> Lens X Y S T -> S -> Y -> T
put lens = Shop.put $ lens $ Shop: id (flip const)

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
